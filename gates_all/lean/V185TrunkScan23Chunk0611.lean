import V185TrunkScan23Chunk0610

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3613104 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2]
def baseStart_3613104 : Nat := 118140960795 + 3613104 * 2 ^ 59
def prefixEnd_3613104 : Nat := 4983230072969 + 3 ^ 40 * 3613104 * 2
def baseEnd_3613104 : Nat := 1855259006682536947683643

theorem tailTrace_3613104 : CollatzResearch.WordTrace tailWord_3613104 prefixEnd_3613104 1855259006682536947683643 := by
  unfold tailWord_3613104
  simp only [CollatzResearch.WordTrace]
  refine ⟨65890364551174375940467183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87853819401565834587289577 65890364551174375940467183)
  ·
    refine ⟨98835546826761563910700775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65890364551174375940467183 98835546826761563910700775)
    ·
      refine ⟨148253320240142345866051163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98835546826761563910700775 148253320240142345866051163)
      ·
        refine ⟨222379980360213518799076745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148253320240142345866051163 222379980360213518799076745)
        ·
          refine ⟨166784985270160139099307559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222379980360213518799076745 166784985270160139099307559)
          ·
            refine ⟨250177477905240208648961339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166784985270160139099307559 250177477905240208648961339)
            ·
              refine ⟨375266216857860312973442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250177477905240208648961339 375266216857860312973442009)
              ·
                refine ⟨281449662643395234730081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375266216857860312973442009 281449662643395234730081507)
                ·
                  refine ⟨422174493965092852095122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281449662643395234730081507 422174493965092852095122261)
                  ·
                    refine ⟨2473678675576715930244857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 422174493965092852095122261 2473678675576715930244857)
                    ·
                      refine ⟨1855259006682536947683643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473678675576715930244857 1855259006682536947683643)
                      ·
                        rfl

theorem cell23_3613104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2].length) (baseStart_3613104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613104 prefixEnd_3613104 := by exact prefixLift 3613104
  have htrace : WordTrace (prefixWord ++ tailWord_3613104) baseStart_3613104 baseEnd_3613104 := by
    simpa [prefixWord, tailWord_3613104, baseEnd_3613104] using wordTrace_append hprefix tailTrace_3613104
  have hstable : (prefixWord ++ tailWord_3613104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613104).length < 2 ^ (prefixWord ++ tailWord_3613104).sum := by decide
  have hdescent : baseEnd_3613104 < baseStart_3613104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613111 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_3613111 : Nat := 118140960795 + 3613111 * 2 ^ 59
def prefixEnd_3613111 : Nat := 4983230072969 + 3 ^ 40 * 3613111 * 2
def baseEnd_3613111 : Nat := 1855262601047118420296111

theorem tailTrace_3613111 : CollatzResearch.WordTrace tailWord_3613111 prefixEnd_3613111 1855262601047118420296111 := by
  unfold tailWord_3613111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131780984413323392076439187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87853989608882261384292791 131780984413323392076439187)
  ·
    refine ⟨197671476619985088114658781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131780984413323392076439187 197671476619985088114658781)
    ·
      refine ⟨74126803732494408042997043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197671476619985088114658781 74126803732494408042997043)
      ·
        refine ⟨111190205598741612064495565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74126803732494408042997043 111190205598741612064495565)
        ·
          refine ⟨41696327099528104524185837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111190205598741612064495565 41696327099528104524185837)
          ·
            refine ⟨15636122662323039196569689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41696327099528104524185837 15636122662323039196569689)
            ·
              refine ⟨11727091996742279397427267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636122662323039196569689 11727091996742279397427267)
              ·
                refine ⟨17590637995113419096140901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727091996742279397427267 17590637995113419096140901)
                ·
                  refine ⟨3298244624083766080526419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17590637995113419096140901 3298244624083766080526419)
                  ·
                    refine ⟨4947366936125649120789629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3298244624083766080526419 4947366936125649120789629)
                    ·
                      refine ⟨1855262601047118420296111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947366936125649120789629 1855262601047118420296111)
                      ·
                        rfl

theorem cell23_3613111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_3613111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613111 prefixEnd_3613111 := by exact prefixLift 3613111
  have htrace : WordTrace (prefixWord ++ tailWord_3613111) baseStart_3613111 baseEnd_3613111 := by
    simpa [prefixWord, tailWord_3613111, baseEnd_3613111] using wordTrace_append hprefix tailTrace_3613111
  have hstable : (prefixWord ++ tailWord_3613111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613111).length < 2 ^ (prefixWord ++ tailWord_3613111).sum := by decide
  have hdescent : baseEnd_3613111 < baseStart_3613111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613128 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3613128 : Nat := 118140960795 + 3613128 * 2 ^ 59
def prefixEnd_3613128 : Nat := 4983230072969 + 3 ^ 40 * 3613128 * 2
def baseEnd_3613128 : Nat := 1855271330218244853783533

theorem tailTrace_3613128 : CollatzResearch.WordTrace tailWord_3613128 prefixEnd_3613128 1855271330218244853783533 := by
  unfold tailWord_3613128
  simp only [CollatzResearch.WordTrace]
  refine ⟨65890802227130901989904019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87854402969507869319872025 65890802227130901989904019)
  ·
    refine ⟨98836203340696352984856029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65890802227130901989904019 98836203340696352984856029)
    ·
      refine ⟨37063576252761132369321011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98836203340696352984856029 37063576252761132369321011)
      ·
        refine ⟨55595364379141698553981517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37063576252761132369321011 55595364379141698553981517)
        ·
          refine ⟨20848261642178136957743069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55595364379141698553981517 20848261642178136957743069)
          ·
            refine ⟨7818098115816801359153651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20848261642178136957743069 7818098115816801359153651)
            ·
              refine ⟨11727147173725202038730477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818098115816801359153651 11727147173725202038730477)
              ·
                refine ⟨4397680190146950764523929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727147173725202038730477 4397680190146950764523929)
                ·
                  refine ⟨3298260142610213073392947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397680190146950764523929 3298260142610213073392947)
                  ·
                    refine ⟨4947390213915319610089421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3298260142610213073392947 4947390213915319610089421)
                    ·
                      refine ⟨1855271330218244853783533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947390213915319610089421 1855271330218244853783533)
                      ·
                        rfl

theorem cell23_3613128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3613128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613128 prefixEnd_3613128 := by exact prefixLift 3613128
  have htrace : WordTrace (prefixWord ++ tailWord_3613128) baseStart_3613128 baseEnd_3613128 := by
    simpa [prefixWord, tailWord_3613128, baseEnd_3613128] using wordTrace_append hprefix tailTrace_3613128
  have hstable : (prefixWord ++ tailWord_3613128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613128).length < 2 ^ (prefixWord ++ tailWord_3613128).sum := by decide
  have hdescent : baseEnd_3613128 < baseStart_3613128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613151 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 4, 2]
def baseStart_3613151 : Nat := 118140960795 + 3613151 * 2 ^ 59
def prefixEnd_3613151 : Nat := 4983230072969 + 3 ^ 40 * 3613151 * 2
def baseEnd_3613151 : Nat := 1855283140273298263795927

theorem tailTrace_3613151 : CollatzResearch.WordTrace tailWord_3613151 prefixEnd_3613151 1855283140273298263795927 := by
  unfold tailWord_3613151
  simp only [CollatzResearch.WordTrace]
  refine ⟨131782443333178478907895307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87854962222118985938596871 131782443333178478907895307)
  ·
    refine ⟨197673664999767718361842961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131782443333178478907895307 197673664999767718361842961)
    ·
      refine ⟨148255248749825788771382221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197673664999767718361842961 148255248749825788771382221)
      ·
        refine ⟨55595718281184670789268333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148255248749825788771382221 55595718281184670789268333)
        ·
          refine ⟨20848394355444251545975625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55595718281184670789268333 20848394355444251545975625)
          ·
            refine ⟨15636295766583188659481719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20848394355444251545975625 15636295766583188659481719)
            ·
              refine ⟨23454443649874782989222579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15636295766583188659481719 23454443649874782989222579)
              ·
                refine ⟨35181665474812174483833869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23454443649874782989222579 35181665474812174483833869)
                ·
                  refine ⟨13193124553054565431437701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35181665474812174483833869 13193124553054565431437701)
                  ·
                    refine ⟨2473710853697731018394569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13193124553054565431437701 2473710853697731018394569)
                    ·
                      refine ⟨1855283140273298263795927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473710853697731018394569 1855283140273298263795927)
                      ·
                        rfl

theorem cell23_3613151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_3613151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613151 prefixEnd_3613151 := by exact prefixLift 3613151
  have htrace : WordTrace (prefixWord ++ tailWord_3613151) baseStart_3613151 baseEnd_3613151 := by
    simpa [prefixWord, tailWord_3613151, baseEnd_3613151] using wordTrace_append hprefix tailTrace_3613151
  have hstable : (prefixWord ++ tailWord_3613151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613151).length < 2 ^ (prefixWord ++ tailWord_3613151).sum := by decide
  have hdescent : baseEnd_3613151 < baseStart_3613151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613164 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_3613164 : Nat := 118140960795 + 3613164 * 2 ^ 59
def prefixEnd_3613164 : Nat := 4983230072969 + 3 ^ 40 * 3613164 * 2
def baseEnd_3613164 : Nat := 1855289815521806712933367

theorem tailTrace_3613164 : CollatzResearch.WordTrace tailWord_3613164 prefixEnd_3613164 1855289815521806712933367 := by
  unfold tailWord_3613164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65891458741065691064059273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87855278321420921418745697 65891458741065691064059273)
  ·
    refine ⟨49418594055799268298044455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65891458741065691064059273 49418594055799268298044455)
    ·
      refine ⟨74127891083698902447066683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49418594055799268298044455 74127891083698902447066683)
      ·
        refine ⟨111191836625548353670600025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74127891083698902447066683 111191836625548353670600025)
        ·
          refine ⟨83393877469161265252950019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111191836625548353670600025 83393877469161265252950019)
          ·
            refine ⟨125090816203741897879425029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83393877469161265252950019 125090816203741897879425029)
            ·
              refine ⟨23454528038201605852392193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125090816203741897879425029 23454528038201605852392193)
              ·
                refine ⟨17590896028651204389294145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23454528038201605852392193 17590896028651204389294145)
                ·
                  refine ⟨13193172021488403291970609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17590896028651204389294145 13193172021488403291970609)
                  ·
                    refine ⟨9894879016116302468977957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13193172021488403291970609 9894879016116302468977957)
                    ·
                      refine ⟨1855289815521806712933367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9894879016116302468977957 1855289815521806712933367)
                      ·
                        rfl

theorem cell23_3613164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_3613164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613164 prefixEnd_3613164 := by exact prefixLift 3613164
  have htrace : WordTrace (prefixWord ++ tailWord_3613164) baseStart_3613164 baseEnd_3613164 := by
    simpa [prefixWord, tailWord_3613164, baseEnd_3613164] using wordTrace_append hprefix tailTrace_3613164
  have hstable : (prefixWord ++ tailWord_3613164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613164).length < 2 ^ (prefixWord ++ tailWord_3613164).sum := by decide
  have hdescent : baseEnd_3613164 < baseStart_3613164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613185 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_3613185 : Nat := 118140960795 + 3613185 * 2 ^ 59
def prefixEnd_3613185 : Nat := 4983230072969 + 3 ^ 40 * 3613185 * 2
def baseEnd_3613185 : Nat := 1855300598615551130770771

theorem tailTrace_3613185 : CollatzResearch.WordTrace tailWord_3613185 prefixEnd_3613185 1855300598615551130770771 := by
  unfold tailWord_3613185
  simp only [CollatzResearch.WordTrace]
  refine ⟨131783683415055302714633009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87855788943370201809755339 131783683415055302714633009)
  ·
    refine ⟨98837762561291477035974757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131783683415055302714633009 98837762561291477035974757)
    ·
      refine ⟨18532080480242151944245267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98837762561291477035974757 18532080480242151944245267)
      ·
        refine ⟨27798120720363227916367901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18532080480242151944245267 27798120720363227916367901)
        ·
          refine ⟨10424295270136210468637963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27798120720363227916367901 10424295270136210468637963)
          ·
            refine ⟨15636442905204315702956945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424295270136210468637963 15636442905204315702956945)
            ·
              refine ⟨11727332178903236777217709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636442905204315702956945 11727332178903236777217709)
              ·
                refine ⟨4397749567088713791456641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727332178903236777217709 4397749567088713791456641)
                ·
                  refine ⟨3298312175316535343592481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397749567088713791456641 3298312175316535343592481)
                  ·
                    refine ⟨2473734131487401507694361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298312175316535343592481 2473734131487401507694361)
                    ·
                      refine ⟨1855300598615551130770771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473734131487401507694361 1855300598615551130770771)
                      ·
                        rfl

theorem cell23_3613185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_3613185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613185 prefixEnd_3613185 := by exact prefixLift 3613185
  have htrace : WordTrace (prefixWord ++ tailWord_3613185) baseStart_3613185 baseEnd_3613185 := by
    simpa [prefixWord, tailWord_3613185, baseEnd_3613185] using wordTrace_append hprefix tailTrace_3613185
  have hstable : (prefixWord ++ tailWord_3613185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613185).length < 2 ^ (prefixWord ++ tailWord_3613185).sum := by decide
  have hdescent : baseEnd_3613185 < baseStart_3613185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613191 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 7]
def baseStart_3613191 : Nat := 118140960795 + 3613191 * 2 ^ 59
def prefixEnd_3613191 : Nat := 4983230072969 + 3 ^ 40 * 3613191 * 2
def baseEnd_3613191 : Nat := 206144853277719789699527

theorem tailTrace_3613191 : CollatzResearch.WordTrace tailWord_3613191 prefixEnd_3613191 206144853277719789699527 := by
  unfold tailWord_3613191
  simp only [CollatzResearch.WordTrace]
  refine ⟨131783902253033565739351427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87855934835355710492900951 131783902253033565739351427)
  ·
    refine ⟨197675853379550348609027141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131783902253033565739351427 197675853379550348609027141)
    ·
      refine ⟨37064222508665690364192589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197675853379550348609027141 37064222508665690364192589)
      ·
        refine ⟨13899083440749633886572221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37064222508665690364192589 13899083440749633886572221)
        ·
          refine ⟨5212156290281112707464583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13899083440749633886572221 5212156290281112707464583)
          ·
            refine ⟨7818234435421669061196875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212156290281112707464583 7818234435421669061196875)
            ·
              refine ⟨11727351653132503591795313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818234435421669061196875 11727351653132503591795313)
              ·
                refine ⟨8795513739849377693846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11727351653132503591795313 8795513739849377693846485)
                ·
                  refine ⟨206144853277719789699527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8795513739849377693846485 206144853277719789699527)
                  ·
                    rfl

theorem cell23_3613191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 7].length) (baseStart_3613191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613191 prefixEnd_3613191 := by exact prefixLift 3613191
  have htrace : WordTrace (prefixWord ++ tailWord_3613191) baseStart_3613191 baseEnd_3613191 := by
    simpa [prefixWord, tailWord_3613191, baseEnd_3613191] using wordTrace_append hprefix tailTrace_3613191
  have hstable : (prefixWord ++ tailWord_3613191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613191).length < 2 ^ (prefixWord ++ tailWord_3613191).sum := by decide
  have hdescent : baseEnd_3613191 < baseStart_3613191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613208 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 5]
def baseStart_3613208 : Nat := 118140960795 + 3613208 * 2 ^ 59
def prefixEnd_3613208 : Nat := 4983230072969 + 3 ^ 40 * 3613208 * 2
def baseEnd_3613208 : Nat := 206145823185622726753685

theorem tailTrace_3613208 : CollatzResearch.WordTrace tailWord_3613208 prefixEnd_3613208 206145823185622726753685 := by
  unfold tailWord_3613208
  simp only [CollatzResearch.WordTrace]
  refine ⟨65892261146985988821360139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87856348195981318428480185 65892261146985988821360139)
  ·
    refine ⟨98838391720478983232040209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65892261146985988821360139 98838391720478983232040209)
    ·
      refine ⟨74128793790359237424030157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98838391720478983232040209 74128793790359237424030157)
      ·
        refine ⟨27798297671384714034011309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74128793790359237424030157 27798297671384714034011309)
        ·
          refine ⟨10424361626769267762754241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27798297671384714034011309 10424361626769267762754241)
          ·
            refine ⟨7818271220076950822065681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10424361626769267762754241 7818271220076950822065681)
            ·
              refine ⟨5863703415057713116549261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818271220076950822065681 5863703415057713116549261)
              ·
                refine ⟨2198888780646642418705973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863703415057713116549261 2198888780646642418705973)
                ·
                  refine ⟨206145823185622726753685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198888780646642418705973 206145823185622726753685)
                  ·
                    rfl

theorem cell23_3613208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 5].length) (baseStart_3613208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613208 prefixEnd_3613208 := by exact prefixLift 3613208
  have htrace : WordTrace (prefixWord ++ tailWord_3613208) baseStart_3613208 baseEnd_3613208 := by
    simpa [prefixWord, tailWord_3613208, baseEnd_3613208] using wordTrace_append hprefix tailTrace_3613208
  have hstable : (prefixWord ++ tailWord_3613208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613208).length < 2 ^ (prefixWord ++ tailWord_3613208).sum := by decide
  have hdescent : baseEnd_3613208 < baseStart_3613208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613236 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3613236 : Nat := 118140960795 + 3613236 * 2 ^ 59
def prefixEnd_3613236 : Nat := 4983230072969 + 3 ^ 40 * 3613236 * 2
def baseEnd_3613236 : Nat := 1855326786128930431233037

theorem tailTrace_3613236 : CollatzResearch.WordTrace tailWord_3613236 prefixEnd_3613236 1855326786128930431233037 := by
  unfold tailWord_3613236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65892771768935269212369781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87857029025247025616493041 65892771768935269212369781)
  ·
    refine ⟨6177447353337681488659667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65892771768935269212369781 6177447353337681488659667)
    ·
      refine ⟨9266171030006522232989501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177447353337681488659667 9266171030006522232989501)
      ·
        refine ⟨3474814136252445837371063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9266171030006522232989501 3474814136252445837371063)
        ·
          refine ⟨5212221204378668756056595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474814136252445837371063 5212221204378668756056595)
          ·
            refine ⟨7818331806568003134084893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212221204378668756056595 7818331806568003134084893)
            ·
              refine ⟨2931874427463001175281835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7818331806568003134084893 2931874427463001175281835)
              ·
                refine ⟨4397811641194501762922753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931874427463001175281835 4397811641194501762922753)
                ·
                  refine ⟨3298358730895876322192065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397811641194501762922753 3298358730895876322192065)
                  ·
                    refine ⟨2473769048171907241644049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298358730895876322192065 2473769048171907241644049)
                    ·
                      refine ⟨1855326786128930431233037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473769048171907241644049 1855326786128930431233037)
                      ·
                        rfl

theorem cell23_3613236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3613236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613236 prefixEnd_3613236 := by exact prefixLift 3613236
  have htrace : WordTrace (prefixWord ++ tailWord_3613236) baseStart_3613236 baseEnd_3613236 := by
    simpa [prefixWord, tailWord_3613236, baseEnd_3613236] using wordTrace_append hprefix tailTrace_3613236
  have hstable : (prefixWord ++ tailWord_3613236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613236).length < 2 ^ (prefixWord ++ tailWord_3613236).sum := by decide
  have hdescent : baseEnd_3613236 < baseStart_3613236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613285 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_3613285 : Nat := 118140960795 + 3613285 * 2 ^ 59
def prefixEnd_3613285 : Nat := 4983230072969 + 3 ^ 40 * 3613285 * 2
def baseEnd_3613285 : Nat := 618450648893666913173437

theorem tailTrace_3613285 : CollatzResearch.WordTrace tailWord_3613285 prefixEnd_3613285 618450648893666913173437 := by
  unfold tailWord_3613285
  simp only [CollatzResearch.WordTrace]
  refine ⟨131787330714693019793273309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87858220476462013195515539 131787330714693019793273309)
  ·
    refine ⟨49420249018009882422477491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131787330714693019793273309 49420249018009882422477491)
    ·
      refine ⟨74130373527014823633716237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49420249018009882422477491 74130373527014823633716237)
      ·
        refine ⟨27798890072630558862643589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74130373527014823633716237 27798890072630558862643589)
        ·
          refine ⟨5212291888618229786745673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27798890072630558862643589 5212291888618229786745673)
          ·
            refine ⟨3909218916463672340059255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5212291888618229786745673 3909218916463672340059255)
            ·
              refine ⟨5863828374695508510088883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909218916463672340059255 5863828374695508510088883)
              ·
                refine ⟨8795742562043262765133325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863828374695508510088883 8795742562043262765133325)
                ·
                  refine ⟨3298403460766223536924997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8795742562043262765133325 3298403460766223536924997)
                  ·
                    refine ⟨618450648893666913173437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298403460766223536924997 618450648893666913173437)
                    ·
                      rfl

theorem cell23_3613285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_3613285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613285 prefixEnd_3613285 := by exact prefixLift 3613285
  have htrace : WordTrace (prefixWord ++ tailWord_3613285) baseStart_3613285 baseEnd_3613285 := by
    simpa [prefixWord, tailWord_3613285, baseEnd_3613285] using wordTrace_append hprefix tailTrace_3613285
  have hstable : (prefixWord ++ tailWord_3613285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613285).length < 2 ^ (prefixWord ++ tailWord_3613285).sum := by decide
  have hdescent : baseEnd_3613285 < baseStart_3613285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613298 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_3613298 : Nat := 118140960795 + 3613298 * 2 ^ 59
def prefixEnd_3613298 : Nat := 4983230072969 + 3 ^ 40 * 3613298 * 2
def baseEnd_3613298 : Nat := 206150957992167687628639

theorem tailTrace_3613298 : CollatzResearch.WordTrace tailWord_3613298 prefixEnd_3613298 206150957992167687628639 := by
  unfold tailWord_3613298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32946951215911480753374137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87858536575763948675664365 32946951215911480753374137)
  ·
    refine ⟨24710213411933610565030603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32946951215911480753374137 24710213411933610565030603)
    ·
      refine ⟨37065320117900415847545905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710213411933610565030603 37065320117900415847545905)
      ·
        refine ⟨27798990088425311885659429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37065320117900415847545905 27798990088425311885659429)
        ·
          refine ⟨5212310641579745978561143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27798990088425311885659429 5212310641579745978561143)
          ·
            refine ⟨7818465962369618967841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212310641579745978561143 7818465962369618967841715)
            ·
              refine ⟨11727698943554428451762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818465962369618967841715 11727698943554428451762573)
              ·
                refine ⟨4397887103832910669410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727698943554428451762573 4397887103832910669410965)
                ·
                  refine ⟨206150957992167687628639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4397887103832910669410965 206150957992167687628639)
                  ·
                    rfl

theorem cell23_3613298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_3613298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613298 prefixEnd_3613298 := by exact prefixLift 3613298
  have htrace : WordTrace (prefixWord ++ tailWord_3613298) baseStart_3613298 baseEnd_3613298 := by
    simpa [prefixWord, tailWord_3613298, baseEnd_3613298] using wordTrace_append hprefix tailTrace_3613298
  have hstable : (prefixWord ++ tailWord_3613298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613298).length < 2 ^ (prefixWord ++ tailWord_3613298).sum := by decide
  have hdescent : baseEnd_3613298 < baseStart_3613298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613304 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_3613304 : Nat := 118140960795 + 3613304 * 2 ^ 59
def prefixEnd_3613304 : Nat := 4983230072969 + 3 ^ 40 * 3613304 * 2
def baseEnd_3613304 : Nat := 1855361702813436165182723

theorem tailTrace_3613304 : CollatzResearch.WordTrace tailWord_3613304 prefixEnd_3613304 1855361702813436165182723 := by
  unfold tailWord_3613304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65894011850812093019107483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87858682467749457358809977 65894011850812093019107483)
  ·
    refine ⟨98841017776218139528661225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65894011850812093019107483 98841017776218139528661225)
    ·
      refine ⟨74130763332163604646495919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98841017776218139528661225 74130763332163604646495919)
      ·
        refine ⟨111196144998245406969743879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74130763332163604646495919 111196144998245406969743879)
        ·
          refine ⟨166794217497368110454615819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111196144998245406969743879 166794217497368110454615819)
          ·
            refine ⟨250191326246052165681923729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166794217497368110454615819 250191326246052165681923729)
            ·
              refine ⟨187643494684539124261442797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250191326246052165681923729 187643494684539124261442797)
              ·
                refine ⟨70366310506702171598041049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187643494684539124261442797 70366310506702171598041049)
                ·
                  refine ⟨52774732880026628698530787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70366310506702171598041049 52774732880026628698530787)
                  ·
                    refine ⟨79162099320039943047796181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52774732880026628698530787 79162099320039943047796181)
                    ·
                      refine ⟨1855361702813436165182723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79162099320039943047796181 1855361702813436165182723)
                      ·
                        rfl

theorem cell23_3613304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_3613304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613304 prefixEnd_3613304 := by exact prefixLift 3613304
  have htrace : WordTrace (prefixWord ++ tailWord_3613304) baseStart_3613304 baseEnd_3613304 := by
    simpa [prefixWord, tailWord_3613304, baseEnd_3613304] using wordTrace_append hprefix tailTrace_3613304
  have hstable : (prefixWord ++ tailWord_3613304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613304).length < 2 ^ (prefixWord ++ tailWord_3613304).sum := by decide
  have hdescent : baseEnd_3613304 < baseStart_3613304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613308 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3613308 : Nat := 118140960795 + 3613308 * 2 ^ 59
def prefixEnd_3613308 : Nat := 4983230072969 + 3 ^ 40 * 3613308 * 2
def baseEnd_3613308 : Nat := 1855363756736054149532705

theorem tailTrace_3613308 : CollatzResearch.WordTrace tailWord_3613308 prefixEnd_3613308 1855363756736054149532705 := by
  unfold tailWord_3613308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65894084796804847360680289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87858779729073129814240385 65894084796804847360680289)
  ·
    refine ⟨49420563597603635520510217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65894084796804847360680289 49420563597603635520510217)
    ·
      refine ⟨37065422698202726640382663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49420563597603635520510217 37065422698202726640382663)
      ·
        refine ⟨55598134047304089960573995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37065422698202726640382663 55598134047304089960573995)
        ·
          refine ⟨83397201070956134940860993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55598134047304089960573995 83397201070956134940860993)
          ·
            refine ⟨62547900803217101205645745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83397201070956134940860993 62547900803217101205645745)
            ·
              refine ⟨46910925602412825904234309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62547900803217101205645745 46910925602412825904234309)
              ·
                refine ⟨8795798550452404857043933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46910925602412825904234309 8795798550452404857043933)
                ·
                  refine ⟨3298424456419651821391475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8795798550452404857043933 3298424456419651821391475)
                  ·
                    refine ⟨4947636684629477732087213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3298424456419651821391475 4947636684629477732087213)
                    ·
                      refine ⟨1855363756736054149532705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947636684629477732087213 1855363756736054149532705)
                      ·
                        rfl

theorem cell23_3613308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3613308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613308 prefixEnd_3613308 := by exact prefixLift 3613308
  have htrace : WordTrace (prefixWord ++ tailWord_3613308) baseStart_3613308 baseEnd_3613308 := by
    simpa [prefixWord, tailWord_3613308, baseEnd_3613308] using wordTrace_append hprefix tailTrace_3613308
  have hstable : (prefixWord ++ tailWord_3613308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613308).length < 2 ^ (prefixWord ++ tailWord_3613308).sum := by decide
  have hdescent : baseEnd_3613308 < baseStart_3613308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613311 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 1, 5]
def baseStart_3613311 : Nat := 118140960795 + 3613311 * 2 ^ 59
def prefixEnd_3613311 : Nat := 4983230072969 + 3 ^ 40 * 3613311 * 2
def baseEnd_3613311 : Nat := 618455099059339212598397

theorem tailTrace_3613311 : CollatzResearch.WordTrace tailWord_3613311 prefixEnd_3613311 618455099059339212598397 := by
  unfold tailWord_3613311
  simp only [CollatzResearch.WordTrace]
  refine ⟨131788279012598826233719787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87858852675065884155813191 131788279012598826233719787)
  ·
    refine ⟨197682418518898239350579681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131788279012598826233719787 197682418518898239350579681)
    ·
      refine ⟨148261813889173679512934761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197682418518898239350579681 148261813889173679512934761)
      ·
        refine ⟨111196360416880259634701071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148261813889173679512934761 111196360416880259634701071)
        ·
          refine ⟨166794540625320389452051607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111196360416880259634701071 166794540625320389452051607)
          ·
            refine ⟨250191810937980584178077411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166794540625320389452051607 250191810937980584178077411)
            ·
              refine ⟨375287716406970876267116117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250191810937980584178077411 375287716406970876267116117)
              ·
                refine ⟨4397902926644189956255267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 375287716406970876267116117 4397902926644189956255267)
                ·
                  refine ⟨6596854389966284934382901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397902926644189956255267 6596854389966284934382901)
                  ·
                    refine ⟨618455099059339212598397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6596854389966284934382901 618455099059339212598397)
                    ·
                      rfl

theorem cell23_3613311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_3613311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613311 prefixEnd_3613311 := by exact prefixLift 3613311
  have htrace : WordTrace (prefixWord ++ tailWord_3613311) baseStart_3613311 baseEnd_3613311 := by
    simpa [prefixWord, tailWord_3613311, baseEnd_3613311] using wordTrace_append hprefix tailTrace_3613311
  have hstable : (prefixWord ++ tailWord_3613311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613311).length < 2 ^ (prefixWord ++ tailWord_3613311).sum := by decide
  have hdescent : baseEnd_3613311 < baseStart_3613311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613455 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 4, 2, 2]
def baseStart_3613455 : Nat := 118140960795 + 3613455 * 2 ^ 59
def prefixEnd_3613455 : Nat := 4983230072969 + 3 ^ 40 * 3613455 * 2
def baseEnd_3613455 : Nat := 1855439238392265074394529

theorem tailTrace_3613455 : CollatzResearch.WordTrace tailWord_3613455 prefixEnd_3613455 1855439238392265074394529 := by
  unfold tailWord_3613455
  simp only [CollatzResearch.WordTrace]
  refine ⟨131793531124077138826961819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87862354082718092551307879 131793531124077138826961819)
  ·
    refine ⟨197690296686115708240442729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131793531124077138826961819 197690296686115708240442729)
    ·
      refine ⟨148267722514586781180332047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197690296686115708240442729 148267722514586781180332047)
      ·
        refine ⟨222401583771880171770498071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148267722514586781180332047 222401583771880171770498071)
        ·
          refine ⟨333602375657820257655747107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222401583771880171770498071 333602375657820257655747107)
          ·
            refine ⟨500403563486730386483620661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333602375657820257655747107 500403563486730386483620661)
            ·
              refine ⟨46912834076880973732839437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 500403563486730386483620661 46912834076880973732839437)
              ·
                refine ⟨17592312778830365149814789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46912834076880973732839437 17592312778830365149814789)
                ·
                  refine ⟨3298558646030693465590273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17592312778830365149814789 3298558646030693465590273)
                  ·
                    refine ⟨2473918984523020099192705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298558646030693465590273 2473918984523020099192705)
                    ·
                      refine ⟨1855439238392265074394529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473918984523020099192705 1855439238392265074394529)
                      ·
                        rfl

theorem cell23_3613455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2, 2].length) (baseStart_3613455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613455 prefixEnd_3613455 := by exact prefixLift 3613455
  have htrace : WordTrace (prefixWord ++ tailWord_3613455) baseStart_3613455 baseEnd_3613455 := by
    simpa [prefixWord, tailWord_3613455, baseEnd_3613455] using wordTrace_append hprefix tailTrace_3613455
  have hstable : (prefixWord ++ tailWord_3613455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613455).length < 2 ^ (prefixWord ++ tailWord_3613455).sum := by decide
  have hdescent : baseEnd_3613455 < baseStart_3613455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613476 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_3613476 : Nat := 118140960795 + 3613476 * 2 ^ 59
def prefixEnd_3613476 : Nat := 4983230072969 + 3 ^ 40 * 3613476 * 2
def baseEnd_3613476 : Nat := 1855450021486009492231933

theorem tailTrace_3613476 : CollatzResearch.WordTrace tailWord_3613476 prefixEnd_3613476 1855450021486009492231933 := by
  unfold tailWord_3613476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65897148528500529706738141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87862864704667372942317521 65897148528500529706738141)
  ·
    refine ⟨24711430698187698640026803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65897148528500529706738141 24711430698187698640026803)
    ·
      refine ⟨37067146047281547960040205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24711430698187698640026803 37067146047281547960040205)
      ·
        refine ⟨13900179767730580485015077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37067146047281547960040205 13900179767730580485015077)
        ·
          refine ⟨2606283706449483840940327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13900179767730580485015077 2606283706449483840940327)
          ·
            refine ⟨3909425559674225761410491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606283706449483840940327 3909425559674225761410491)
            ·
              refine ⟨5864138339511338642115737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909425559674225761410491 5864138339511338642115737)
              ·
                refine ⟨4398103754633503981586803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5864138339511338642115737 4398103754633503981586803)
                ·
                  refine ⟨6597155631950255972380205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398103754633503981586803 6597155631950255972380205)
                  ·
                    refine ⟨2473933361981345989642577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6597155631950255972380205 2473933361981345989642577)
                    ·
                      refine ⟨1855450021486009492231933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473933361981345989642577 1855450021486009492231933)
                      ·
                        rfl

theorem cell23_3613476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_3613476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613476 prefixEnd_3613476 := by exact prefixLift 3613476
  have htrace : WordTrace (prefixWord ++ tailWord_3613476) baseStart_3613476 baseEnd_3613476 := by
    simpa [prefixWord, tailWord_3613476, baseEnd_3613476] using wordTrace_append hprefix tailTrace_3613476
  have hstable : (prefixWord ++ tailWord_3613476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613476).length < 2 ^ (prefixWord ++ tailWord_3613476).sum := by decide
  have hdescent : baseEnd_3613476 < baseStart_3613476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613528 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3613528 : Nat := 118140960795 + 3613528 * 2 ^ 59
def prefixEnd_3613528 : Nat := 4983230072969 + 3 ^ 40 * 3613528 * 2
def baseEnd_3613528 : Nat := 1855476722480043288781693

theorem tailTrace_3613528 : CollatzResearch.WordTrace tailWord_3613528 prefixEnd_3613528 1855476722480043288781693 := by
  unfold tailWord_3613528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65898096826406336147184619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87864129101875114862912825 65898096826406336147184619)
  ·
    refine ⟨98847145239609504220776929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65898096826406336147184619 98847145239609504220776929)
    ·
      refine ⟨74135358929707128165582697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98847145239609504220776929 74135358929707128165582697)
      ·
        refine ⟨55601519197280346124187023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74135358929707128165582697 55601519197280346124187023)
        ·
          refine ⟨83402278795920519186280535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55601519197280346124187023 83402278795920519186280535)
          ·
            refine ⟨125103418193880778779420803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83402278795920519186280535 125103418193880778779420803)
            ·
              refine ⟨187655127290821168169131205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125103418193880778779420803 187655127290821168169131205)
              ·
                refine ⟨35185336367028969031712101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187655127290821168169131205 35185336367028969031712101)
                ·
                  refine ⟨6597250568817931693446019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35185336367028969031712101 6597250568817931693446019)
                  ·
                    refine ⟨9895875853226897540169029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597250568817931693446019 9895875853226897540169029)
                    ·
                      refine ⟨1855476722480043288781693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9895875853226897540169029 1855476722480043288781693)
                      ·
                        rfl

theorem cell23_3613528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3613528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613528 prefixEnd_3613528 := by exact prefixLift 3613528
  have htrace : WordTrace (prefixWord ++ tailWord_3613528) baseStart_3613528 baseEnd_3613528 := by
    simpa [prefixWord, tailWord_3613528, baseEnd_3613528] using wordTrace_append hprefix tailTrace_3613528
  have hstable : (prefixWord ++ tailWord_3613528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613528).length < 2 ^ (prefixWord ++ tailWord_3613528).sum := by decide
  have hdescent : baseEnd_3613528 < baseStart_3613528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613565 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_3613565 : Nat := 118140960795 + 3613565 * 2 ^ 59
def prefixEnd_3613565 : Nat := 4983230072969 + 3 ^ 40 * 3613565 * 2
def baseEnd_3613565 : Nat := 1855495721264259644019023

theorem tailTrace_3613565 : CollatzResearch.WordTrace tailWord_3613565 prefixEnd_3613565 1855495721264259644019023 := by
  unfold tailWord_3613565
  simp only [CollatzResearch.WordTrace]
  refine ⟨131797543153678627613466149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87865028769119085075644099 131797543153678627613466149)
  ·
    refine ⟨24712039341314742677524903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131797543153678627613466149 24712039341314742677524903)
    ·
      refine ⟨37068059011972114016287355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24712039341314742677524903 37068059011972114016287355)
      ·
        refine ⟨55602088517958171024431033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37068059011972114016287355 55602088517958171024431033)
        ·
          refine ⟨41701566388468628268323275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55602088517958171024431033 41701566388468628268323275)
          ·
            refine ⟨62552349582702942402484913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41701566388468628268323275 62552349582702942402484913)
            ·
              refine ⟨46914262187027206801863685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62552349582702942402484913 46914262187027206801863685)
              ·
                refine ⟨8796424160067601275349441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46914262187027206801863685 8796424160067601275349441)
                ·
                  refine ⟨6597318120050700956512081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8796424160067601275349441 6597318120050700956512081)
                  ·
                    refine ⟨4947988590038025717384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597318120050700956512081 4947988590038025717384061)
                    ·
                      refine ⟨1855495721264259644019023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947988590038025717384061 1855495721264259644019023)
                      ·
                        rfl

theorem cell23_3613565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_3613565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613565 prefixEnd_3613565 := by exact prefixLift 3613565
  have htrace : WordTrace (prefixWord ++ tailWord_3613565) baseStart_3613565 baseEnd_3613565 := by
    simpa [prefixWord, tailWord_3613565, baseEnd_3613565] using wordTrace_append hprefix tailTrace_3613565
  have hstable : (prefixWord ++ tailWord_3613565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613565).length < 2 ^ (prefixWord ++ tailWord_3613565).sum := by decide
  have hdescent : baseEnd_3613565 < baseStart_3613565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613568 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 6]
def baseStart_3613568 : Nat := 118140960795 + 3613568 * 2 ^ 59
def prefixEnd_3613568 : Nat := 4983230072969 + 3 ^ 40 * 3613568 * 2
def baseEnd_3613568 : Nat := 206166362411802570253501

theorem tailTrace_3613568 : CollatzResearch.WordTrace tailWord_3613568 prefixEnd_3613568 206166362411802570253501 := by
  unfold tailWord_3613568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65898826286333879562912679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87865101715111839417216905 65898826286333879562912679)
  ·
    refine ⟨98848239429500819344369019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65898826286333879562912679 98848239429500819344369019)
    ·
      refine ⟨148272359144251229016553529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98848239429500819344369019 148272359144251229016553529)
      ·
        refine ⟨111204269358188421762415147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148272359144251229016553529 111204269358188421762415147)
        ·
          refine ⟨166806404037282632643622721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111204269358188421762415147 166806404037282632643622721)
          ·
            refine ⟨125104803027961974482717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166806404037282632643622721 125104803027961974482717041)
            ·
              refine ⟨93828602270971480862037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125104803027961974482717041 93828602270971480862037781)
              ·
                refine ⟨4398215731451788165408021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93828602270971480862037781 4398215731451788165408021)
                ·
                  refine ⟨206166362411802570253501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4398215731451788165408021 206166362411802570253501)
                  ·
                    rfl

theorem cell23_3613568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_3613568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613568 prefixEnd_3613568 := by exact prefixLift 3613568
  have htrace : WordTrace (prefixWord ++ tailWord_3613568) baseStart_3613568 baseEnd_3613568 := by
    simpa [prefixWord, tailWord_3613568, baseEnd_3613568] using wordTrace_append hprefix tailTrace_3613568
  have hstable : (prefixWord ++ tailWord_3613568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613568).length < 2 ^ (prefixWord ++ tailWord_3613568).sum := by decide
  have hdescent : baseEnd_3613568 < baseStart_3613568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613636 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 6]
def baseStart_3613636 : Nat := 118140960795 + 3613636 * 2 ^ 59
def prefixEnd_3613636 : Nat := 4983230072969 + 3 ^ 40 * 3613636 * 2
def baseEnd_3613636 : Nat := 206170242043414318470133

theorem tailTrace_3613636 : CollatzResearch.WordTrace tailWord_3613636 prefixEnd_3613636 206170242043414318470133 := by
  unfold tailWord_3613636
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900066368210703369650381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87866755157614271159533841 65900066368210703369650381)
  ·
    refine ⟨24712524888079013763618893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65900066368210703369650381 24712524888079013763618893)
    ·
      refine ⟨9267196833029630161357085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24712524888079013763618893 9267196833029630161357085)
      ·
        refine ⟨3475198812386111310508907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9267196833029630161357085 3475198812386111310508907)
        ·
          refine ⟨5212798218579166965763361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475198812386111310508907 5212798218579166965763361)
          ·
            refine ⟨3909598663934375224322521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5212798218579166965763361 3909598663934375224322521)
            ·
              refine ⟨2932198997950781418241891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909598663934375224322521 2932198997950781418241891)
              ·
                refine ⟨4398298496926172127362837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932198997950781418241891 4398298496926172127362837)
                ·
                  refine ⟨206170242043414318470133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4398298496926172127362837 206170242043414318470133)
                  ·
                    rfl

theorem cell23_3613636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_3613636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613636 prefixEnd_3613636 := by exact prefixLift 3613636
  have htrace : WordTrace (prefixWord ++ tailWord_3613636) baseStart_3613636 baseEnd_3613636 := by
    simpa [prefixWord, tailWord_3613636, baseEnd_3613636] using wordTrace_append hprefix tailTrace_3613636
  have hstable : (prefixWord ++ tailWord_3613636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613636).length < 2 ^ (prefixWord ++ tailWord_3613636).sum := by decide
  have hdescent : baseEnd_3613636 < baseStart_3613636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613652 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3613652 : Nat := 118140960795 + 3613652 * 2 ^ 59
def prefixEnd_3613652 : Nat := 4983230072969 + 3 ^ 40 * 3613652 * 2
def baseEnd_3613652 : Nat := 1855540394081200803631123

theorem tailTrace_3613652 : CollatzResearch.WordTrace tailWord_3613652 prefixEnd_3613652 1855540394081200803631123 := by
  unfold tailWord_3613652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900358152181720735941605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87867144202908960981255473 65900358152181720735941605)
  ·
    refine ⟨12356317153534072637989051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65900358152181720735941605 12356317153534072637989051)
    ·
      refine ⟨18534475730301108956983577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356317153534072637989051 18534475730301108956983577)
      ·
        refine ⟨13900856797725831717737683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18534475730301108956983577 13900856797725831717737683)
        ·
          refine ⟨20851285196588747576606525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13900856797725831717737683 20851285196588747576606525)
          ·
            refine ⟨7819231948720780341227447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20851285196588747576606525 7819231948720780341227447)
            ·
              refine ⟨11728847923081170511841171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819231948720780341227447 11728847923081170511841171)
              ·
                refine ⟨17593271884621755767761757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728847923081170511841171 17593271884621755767761757)
                ·
                  refine ⟨6597476956733158412910659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593271884621755767761757 6597476956733158412910659)
                  ·
                    refine ⟨9896215435099737619365989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597476956733158412910659 9896215435099737619365989)
                    ·
                      refine ⟨1855540394081200803631123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9896215435099737619365989 1855540394081200803631123)
                      ·
                        rfl

theorem cell23_3613652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3613652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613652 prefixEnd_3613652 := by exact prefixLift 3613652
  have htrace : WordTrace (prefixWord ++ tailWord_3613652) baseStart_3613652 baseEnd_3613652 := by
    simpa [prefixWord, tailWord_3613652, baseEnd_3613652] using wordTrace_append hprefix tailTrace_3613652
  have hstable : (prefixWord ++ tailWord_3613652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613652).length < 2 ^ (prefixWord ++ tailWord_3613652).sum := by decide
  have hdescent : baseEnd_3613652 < baseStart_3613652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613666 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3613666 : Nat := 118140960795 + 3613666 * 2 ^ 59
def prefixEnd_3613666 : Nat := 4983230072969 + 3 ^ 40 * 3613666 * 2
def baseEnd_3613666 : Nat := 618515860936787916285353

theorem tailTrace_3613666 : CollatzResearch.WordTrace tailWord_3613666 prefixEnd_3613666 618515860936787916285353 := by
  unfold tailWord_3613666
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950306731578180465723213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87867484617541814575261901 32950306731578180465723213)
  ·
    refine ⟨12356365024341817674646205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32950306731578180465723213 12356365024341817674646205)
    ·
      refine ⟨4633636884128181627992327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12356365024341817674646205 4633636884128181627992327)
      ·
        refine ⟨6950455326192272441988491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633636884128181627992327 6950455326192272441988491)
        ·
          refine ⟨10425682989288408662982737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950455326192272441988491 10425682989288408662982737)
          ·
            refine ⟨7819262241966306497237053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10425682989288408662982737 7819262241966306497237053)
            ·
              refine ⟨2932223340737364936463895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7819262241966306497237053 2932223340737364936463895)
              ·
                refine ⟨4398335011106047404695843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932223340737364936463895 4398335011106047404695843)
                ·
                  refine ⟨6597502516659071107043765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398335011106047404695843 6597502516659071107043765)
                  ·
                    refine ⟨618515860936787916285353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6597502516659071107043765 618515860936787916285353)
                    ·
                      rfl

theorem cell23_3613666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3613666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613666 prefixEnd_3613666 := by exact prefixLift 3613666
  have htrace : WordTrace (prefixWord ++ tailWord_3613666) baseStart_3613666 baseEnd_3613666 := by
    simpa [prefixWord, tailWord_3613666, baseEnd_3613666] using wordTrace_append hprefix tailTrace_3613666
  have hstable : (prefixWord ++ tailWord_3613666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613666).length < 2 ^ (prefixWord ++ tailWord_3613666).sum := by decide
  have hdescent : baseEnd_3613666 < baseStart_3613666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613672 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3613672 : Nat := 118140960795 + 3613672 * 2 ^ 59
def prefixEnd_3613672 : Nat := 4983230072969 + 3 ^ 40 * 3613672 * 2
def baseEnd_3613672 : Nat := 1855550663694290725381031

theorem tailTrace_3613672 : CollatzResearch.WordTrace tailWord_3613672 prefixEnd_3613672 1855550663694290725381031 := by
  unfold tailWord_3613672
  simp only [CollatzResearch.WordTrace]
  refine ⟨65900722882145492443805635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87867630509527323258407513 65900722882145492443805635)
  ·
    refine ⟨98851084323218238665708453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65900722882145492443805635 98851084323218238665708453)
    ·
      refine ⟨18534578310603419749820335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98851084323218238665708453 18534578310603419749820335)
      ·
        refine ⟨27801867465905129624730503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534578310603419749820335 27801867465905129624730503)
        ·
          refine ⟨41702801198857694437095755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27801867465905129624730503 41702801198857694437095755)
          ·
            refine ⟨62554201798286541655643633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41702801198857694437095755 62554201798286541655643633)
            ·
              refine ⟨46915651348714906241732725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62554201798286541655643633 46915651348714906241732725)
              ·
                refine ⟨4398342313942022460162443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46915651348714906241732725 4398342313942022460162443)
                ·
                  refine ⟨6597513470913033690243665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398342313942022460162443 6597513470913033690243665)
                  ·
                    refine ⟨4948135103184775267682749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597513470913033690243665 4948135103184775267682749)
                    ·
                      refine ⟨1855550663694290725381031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948135103184775267682749 1855550663694290725381031)
                      ·
                        rfl

theorem cell23_3613672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3613672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613672 prefixEnd_3613672 := by exact prefixLift 3613672
  have htrace : WordTrace (prefixWord ++ tailWord_3613672) baseStart_3613672 baseEnd_3613672 := by
    simpa [prefixWord, tailWord_3613672, baseEnd_3613672] using wordTrace_append hprefix tailTrace_3613672
  have hstable : (prefixWord ++ tailWord_3613672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613672).length < 2 ^ (prefixWord ++ tailWord_3613672).sum := by decide
  have hdescent : baseEnd_3613672 < baseStart_3613672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613765 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 7]
def baseStart_3613765 : Nat := 118140960795 + 3613765 * 2 ^ 59
def prefixEnd_3613765 : Nat := 4983230072969 + 3 ^ 40 * 3613765 * 2
def baseEnd_3613765 : Nat := 206177601932795429057567

theorem tailTrace_3613765 : CollatzResearch.WordTrace tailWord_3613765 prefixEnd_3613765 206177601932795429057567 := by
  unfold tailWord_3613765
  simp only [CollatzResearch.WordTrace]
  refine ⟨131804837752954061770746749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87869891835302707847164499 131804837752954061770746749)
  ·
    refine ⟨49426814157357773164030031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131804837752954061770746749 49426814157357773164030031)
    ·
      refine ⟨74140221236036659746045047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49426814157357773164030031 74140221236036659746045047)
      ·
        refine ⟨111210331854054989619067571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74140221236036659746045047 111210331854054989619067571)
        ·
          refine ⟨166815497781082484428601357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111210331854054989619067571 166815497781082484428601357)
          ·
            refine ⟨62555811667905931660725509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166815497781082484428601357 62555811667905931660725509)
            ·
              refine ⟨11729214687732362186386033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62555811667905931660725509 11729214687732362186386033)
              ·
                refine ⟨8796911015799271639789525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11729214687732362186386033 8796911015799271639789525)
                ·
                  refine ⟨206177601932795429057567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8796911015799271639789525 206177601932795429057567)
                  ·
                    rfl

theorem cell23_3613765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_3613765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613765 prefixEnd_3613765 := by exact prefixLift 3613765
  have htrace : WordTrace (prefixWord ++ tailWord_3613765) baseStart_3613765 baseEnd_3613765 := by
    simpa [prefixWord, tailWord_3613765, baseEnd_3613765] using wordTrace_append hprefix tailTrace_3613765
  have hstable : (prefixWord ++ tailWord_3613765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613765).length < 2 ^ (prefixWord ++ tailWord_3613765).sum := by decide
  have hdescent : baseEnd_3613765 < baseStart_3613765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613829 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_3613829 : Nat := 118140960795 + 3613829 * 2 ^ 59
def prefixEnd_3613829 : Nat := 4983230072969 + 3 ^ 40 * 3613829 * 2
def baseEnd_3613829 : Nat := 618543760052348870372603

theorem tailTrace_3613829 : CollatzResearch.WordTrace tailWord_3613829 prefixEnd_3613829 618543760052348870372603 := by
  unfold tailWord_3613829
  simp only [CollatzResearch.WordTrace]
  refine ⟨131807172024722200701076541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87871448016481467134051027 131807172024722200701076541)
  ·
    refine ⟨49427689509270825262903703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131807172024722200701076541 49427689509270825262903703)
    ·
      refine ⟨74141534263906237894355555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49427689509270825262903703 74141534263906237894355555)
      ·
        refine ⟨111212301395859356841533333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74141534263906237894355555 111212301395859356841533333)
        ·
          refine ⟨5213076627930907351946875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111212301395859356841533333 5213076627930907351946875)
          ·
            refine ⟨7819614941896361027920313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213076627930907351946875 7819614941896361027920313)
            ·
              refine ⟨5864711206422270770940235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819614941896361027920313 5864711206422270770940235)
              ·
                refine ⟨8797066809633406156410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864711206422270770940235 8797066809633406156410353)
                ·
                  refine ⟨6597800107225054617307765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8797066809633406156410353 6597800107225054617307765)
                  ·
                    refine ⟨618543760052348870372603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6597800107225054617307765 618543760052348870372603)
                    ·
                      rfl

theorem cell23_3613829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_3613829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613829 prefixEnd_3613829 := by exact prefixLift 3613829
  have htrace : WordTrace (prefixWord ++ tailWord_3613829) baseStart_3613829 baseEnd_3613829 := by
    simpa [prefixWord, tailWord_3613829, baseEnd_3613829] using wordTrace_append hprefix tailTrace_3613829
  have hstable : (prefixWord ++ tailWord_3613829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613829).length < 2 ^ (prefixWord ++ tailWord_3613829).sum := by decide
  have hdescent : baseEnd_3613829 < baseStart_3613829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613866 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3613866 : Nat := 118140960795 + 3613866 * 2 ^ 59
def prefixEnd_3613866 : Nat := 4983230072969 + 3 ^ 40 * 3613866 * 2
def baseEnd_3613866 : Nat := 1855650278941262966355139

theorem tailTrace_3613866 : CollatzResearch.WordTrace tailWord_3613866 prefixEnd_3613866 1855650278941262966355139 := by
  unfold tailWord_3613866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952130381397039005043363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87872347683725437346782301 32952130381397039005043363)
  ·
    refine ⟨49428195572095558507565045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32952130381397039005043363 49428195572095558507565045)
    ·
      refine ⟨4633893334883958610084223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49428195572095558507565045 4633893334883958610084223)
      ·
        refine ⟨6950840002325937915126335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633893334883958610084223 6950840002325937915126335)
        ·
          refine ⟨10426260003488906872689503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950840002325937915126335 10426260003488906872689503)
          ·
            refine ⟨15639390005233360309034255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426260003488906872689503 15639390005233360309034255)
            ·
              refine ⟨23459085007850040463551383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15639390005233360309034255 23459085007850040463551383)
              ·
                refine ⟨35188627511775060695327075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23459085007850040463551383 35188627511775060695327075)
                ·
                  refine ⟨52782941267662591042990613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35188627511775060695327075 52782941267662591042990613)
                  ·
                    refine ⟨2474200371921683955140185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52782941267662591042990613 2474200371921683955140185)
                    ·
                      refine ⟨1855650278941262966355139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474200371921683955140185 1855650278941262966355139)
                      ·
                        rfl

theorem cell23_3613866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3613866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613866 prefixEnd_3613866 := by exact prefixLift 3613866
  have htrace : WordTrace (prefixWord ++ tailWord_3613866) baseStart_3613866 baseEnd_3613866 := by
    simpa [prefixWord, tailWord_3613866, baseEnd_3613866] using wordTrace_append hprefix tailTrace_3613866
  have hstable : (prefixWord ++ tailWord_3613866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613866).length < 2 ^ (prefixWord ++ tailWord_3613866).sum := by decide
  have hdescent : baseEnd_3613866 < baseStart_3613866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613886 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3613886 : Nat := 118140960795 + 3613886 * 2 ^ 59
def prefixEnd_3613886 : Nat := 4983230072969 + 3 ^ 40 * 3613886 * 2
def baseEnd_3613886 : Nat := 1855660548554352888105047

theorem tailTrace_3613886 : CollatzResearch.WordTrace tailWord_3613886 prefixEnd_3613886 1855660548554352888105047 := by
  unfold tailWord_3613886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476156373189462429487689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87872833990343799623934341 16476156373189462429487689)
  ·
    refine ⟨12357117279892096822115767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16476156373189462429487689 12357117279892096822115767)
    ·
      refine ⟨18535675919838145233173651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12357117279892096822115767 18535675919838145233173651)
      ·
        refine ⟨27803513879757217849760477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18535675919838145233173651 27803513879757217849760477)
        ·
          refine ⟨10426317704908956693660179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27803513879757217849760477 10426317704908956693660179)
          ·
            refine ⟨15639476557363435040490269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426317704908956693660179 15639476557363435040490269)
            ·
              refine ⟨5864803709011288140183851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15639476557363435040490269 5864803709011288140183851)
              ·
                refine ⟨8797205563516932210275777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864803709011288140183851 8797205563516932210275777)
                ·
                  refine ⟨6597904172637699157706833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8797205563516932210275777 6597904172637699157706833)
                  ·
                    refine ⟨4948428129478274368280125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597904172637699157706833 4948428129478274368280125)
                    ·
                      refine ⟨1855660548554352888105047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948428129478274368280125 1855660548554352888105047)
                      ·
                        rfl

theorem cell23_3613886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3613886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613886 prefixEnd_3613886 := by exact prefixLift 3613886
  have htrace : WordTrace (prefixWord ++ tailWord_3613886) baseStart_3613886 baseEnd_3613886 := by
    simpa [prefixWord, tailWord_3613886, baseEnd_3613886] using wordTrace_append hprefix tailTrace_3613886
  have hstable : (prefixWord ++ tailWord_3613886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613886).length < 2 ^ (prefixWord ++ tailWord_3613886).sum := by decide
  have hdescent : baseEnd_3613886 < baseStart_3613886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613939 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 4]
def baseStart_3613939 : Nat := 118140960795 + 3613939 * 2 ^ 59
def prefixEnd_3613939 : Nat := 4983230072969 + 3 ^ 40 * 3613939 * 2
def baseEnd_3613939 : Nat := 1855687763029041180742303

theorem tailTrace_3613939 : CollatzResearch.WordTrace tailWord_3613939 prefixEnd_3613939 1855687763029041180742303 := by
  unfold tailWord_3613939
  simp only [CollatzResearch.WordTrace]
  refine ⟨131811184054323689487580871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87874122702882459658387247 131811184054323689487580871)
  ·
    refine ⟨197716776081485534231371307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131811184054323689487580871 197716776081485534231371307)
    ·
      refine ⟨296575164122228301347056961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197716776081485534231371307 296575164122228301347056961)
      ·
        refine ⟨222431373091671226010292721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296575164122228301347056961 222431373091671226010292721)
        ·
          refine ⟨166823529818753419507719541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222431373091671226010292721 166823529818753419507719541)
          ·
            refine ⟨15639705920508133078848707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166823529818753419507719541 15639705920508133078848707)
            ·
              refine ⟨23459558880762199618273061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15639705920508133078848707 23459558880762199618273061)
              ·
                refine ⟨4398667290142912428426199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23459558880762199618273061 4398667290142912428426199)
                ·
                  refine ⟨6598000935214368642639299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398667290142912428426199 6598000935214368642639299)
                  ·
                    refine ⟨9897001402821552963958949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598000935214368642639299 9897001402821552963958949)
                    ·
                      refine ⟨1855687763029041180742303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9897001402821552963958949 1855687763029041180742303)
                      ·
                        rfl

theorem cell23_3613939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_3613939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613939 prefixEnd_3613939 := by exact prefixLift 3613939
  have htrace : WordTrace (prefixWord ++ tailWord_3613939) baseStart_3613939 baseEnd_3613939 := by
    simpa [prefixWord, tailWord_3613939, baseEnd_3613939] using wordTrace_append hprefix tailTrace_3613939
  have hstable : (prefixWord ++ tailWord_3613939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613939).length < 2 ^ (prefixWord ++ tailWord_3613939).sum := by decide
  have hdescent : baseEnd_3613939 < baseStart_3613939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613950 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3613950 : Nat := 118140960795 + 3613950 * 2 ^ 59
def prefixEnd_3613950 : Nat := 4983230072969 + 3 ^ 40 * 3613950 * 2
def baseEnd_3613950 : Nat := 1855693411316240637704753

theorem tailTrace_3613950 : CollatzResearch.WordTrace tailWord_3613950 prefixEnd_3613950 1855693411316240637704753 := by
  unfold tailWord_3613950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476448157160479795778913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87874390171522558910820869 16476448157160479795778913)
  ·
    refine ⟨12357336117870359846834185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16476448157160479795778913 12357336117870359846834185)
    ·
      refine ⟨9268002088402769885125639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12357336117870359846834185 9268002088402769885125639)
      ·
        refine ⟨13902003132604154827688459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268002088402769885125639 13902003132604154827688459)
        ·
          refine ⟨20853004698906232241532689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902003132604154827688459 20853004698906232241532689)
          ·
            refine ⟨15639753524179674181149517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20853004698906232241532689 15639753524179674181149517)
            ·
              refine ⟨5864907571567377817931069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15639753524179674181149517 5864907571567377817931069)
              ·
                refine ⟨2199340339337766681724151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864907571567377817931069 2199340339337766681724151)
                ·
                  refine ⟨3299010509006650022586227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199340339337766681724151 3299010509006650022586227)
                  ·
                    refine ⟨4948515763509975033879341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299010509006650022586227 4948515763509975033879341)
                    ·
                      refine ⟨1855693411316240637704753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948515763509975033879341 1855693411316240637704753)
                      ·
                        rfl

theorem cell23_3613950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3613950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613950 prefixEnd_3613950 := by exact prefixLift 3613950
  have htrace : WordTrace (prefixWord ++ tailWord_3613950) baseStart_3613950 baseEnd_3613950 := by
    simpa [prefixWord, tailWord_3613950, baseEnd_3613950] using wordTrace_append hprefix tailTrace_3613950
  have hstable : (prefixWord ++ tailWord_3613950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613950).length < 2 ^ (prefixWord ++ tailWord_3613950).sum := by decide
  have hdescent : baseEnd_3613950 < baseStart_3613950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613952 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_3613952 : Nat := 118140960795 + 3613952 * 2 ^ 59
def prefixEnd_3613952 : Nat := 4983230072969 + 3 ^ 40 * 3613952 * 2
def baseEnd_3613952 : Nat := 1855694438277549629879743

theorem tailTrace_3613952 : CollatzResearch.WordTrace tailWord_3613952 prefixEnd_3613952 1855694438277549629879743 := by
  unfold tailWord_3613952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65905829101638296353902055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87874438802184395138536073 65905829101638296353902055)
  ·
    refine ⟨98858743652457444530853083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65905829101638296353902055 98858743652457444530853083)
    ·
      refine ⟨148288115478686166796279625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98858743652457444530853083 148288115478686166796279625)
      ·
        refine ⟨111216086609014625097209719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148288115478686166796279625 111216086609014625097209719)
        ·
          refine ⟨166824129913521937645814579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111216086609014625097209719 166824129913521937645814579)
          ·
            refine ⟨250236194870282906468721869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166824129913521937645814579 250236194870282906468721869)
            ·
              refine ⟨93838573076356089925770701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250236194870282906468721869 93838573076356089925770701)
              ·
                refine ⟨35189464903633533722164013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93838573076356089925770701 35189464903633533722164013)
                ·
                  refine ⟨13196049338862575145811505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35189464903633533722164013 13196049338862575145811505)
                  ·
                    refine ⟨9897037004146931359358629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13196049338862575145811505 9897037004146931359358629)
                    ·
                      refine ⟨1855694438277549629879743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9897037004146931359358629 1855694438277549629879743)
                      ·
                        rfl

theorem cell23_3613952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_3613952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613952 prefixEnd_3613952 := by exact prefixLift 3613952
  have htrace : WordTrace (prefixWord ++ tailWord_3613952) baseStart_3613952 baseEnd_3613952 := by
    simpa [prefixWord, tailWord_3613952, baseEnd_3613952] using wordTrace_append hprefix tailTrace_3613952
  have hstable : (prefixWord ++ tailWord_3613952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613952).length < 2 ^ (prefixWord ++ tailWord_3613952).sum := by decide
  have hdescent : baseEnd_3613952 < baseStart_3613952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613956 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3613956 : Nat := 118140960795 + 3613956 * 2 ^ 59
def prefixEnd_3613956 : Nat := 4983230072969 + 3 ^ 40 * 3613956 * 2
def baseEnd_3613956 : Nat := 1855696492200167614229725

theorem tailTrace_3613956 : CollatzResearch.WordTrace tailWord_3613956 prefixEnd_3613956 1855696492200167614229725 := by
  unfold tailWord_3613956
  simp only [CollatzResearch.WordTrace]
  refine ⟨65905902047631050695474861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87874536063508067593966481 65905902047631050695474861)
  ·
    refine ⟨24714713267861644010803073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65905902047631050695474861 24714713267861644010803073)
    ·
      refine ⟨18536034950896233008102305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24714713267861644010803073 18536034950896233008102305)
      ·
        refine ⟨13902026213172174756076729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18536034950896233008102305 13902026213172174756076729)
        ·
          refine ⟨10426519659879131067057547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13902026213172174756076729 10426519659879131067057547)
          ·
            refine ⟨15639779489818696600586321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426519659879131067057547 15639779489818696600586321)
            ·
              refine ⟨11729834617364022450439741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15639779489818696600586321 11729834617364022450439741)
              ·
                refine ⟨4398687981511508418914903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11729834617364022450439741 4398687981511508418914903)
                ·
                  refine ⟨6598031972267262628372355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398687981511508418914903 6598031972267262628372355)
                  ·
                    refine ⟨9897047958400893942558533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598031972267262628372355 9897047958400893942558533)
                    ·
                      refine ⟨1855696492200167614229725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9897047958400893942558533 1855696492200167614229725)
                      ·
                        rfl

theorem cell23_3613956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3613956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613956 prefixEnd_3613956 := by exact prefixLift 3613956
  have htrace : WordTrace (prefixWord ++ tailWord_3613956) baseStart_3613956 baseEnd_3613956 := by
    simpa [prefixWord, tailWord_3613956, baseEnd_3613956] using wordTrace_append hprefix tailTrace_3613956
  have hstable : (prefixWord ++ tailWord_3613956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613956).length < 2 ^ (prefixWord ++ tailWord_3613956).sum := by decide
  have hdescent : baseEnd_3613956 < baseStart_3613956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614023 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3614023 : Nat := 118140960795 + 3614023 * 2 ^ 59
def prefixEnd_3614023 : Nat := 4983230072969 + 3 ^ 40 * 3614023 * 2
def baseEnd_3614023 : Nat := 1855730895404018852091917

theorem tailTrace_3614023 : CollatzResearch.WordTrace tailWord_3614023 prefixEnd_3614023 1855730895404018852091917 := by
  unfold tailWord_3614023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131814247786019371833638723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87876165190679581222425815 131814247786019371833638723)
  ·
    refine ⟨197721371679029057750458085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131814247786019371833638723 197721371679029057750458085)
    ·
      refine ⟨37072757189817948328210891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197721371679029057750458085 37072757189817948328210891)
      ·
        refine ⟨55609135784726922492316337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37072757189817948328210891 55609135784726922492316337)
        ·
          refine ⟨41706851838545191869237253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55609135784726922492316337 41706851838545191869237253)
          ·
            refine ⟨7820034719727223475481985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41706851838545191869237253 7820034719727223475481985)
            ·
              refine ⟨5865026039795417606611489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820034719727223475481985 5865026039795417606611489)
              ·
                refine ⟨4398769529846563204958617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865026039795417606611489 4398769529846563204958617)
                ·
                  refine ⟨3299077147384922403718963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398769529846563204958617 3299077147384922403718963)
                  ·
                    refine ⟨4948615721077383605578445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299077147384922403718963 4948615721077383605578445)
                    ·
                      refine ⟨1855730895404018852091917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948615721077383605578445 1855730895404018852091917)
                      ·
                        rfl

theorem cell23_3614023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3614023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614023 prefixEnd_3614023 := by exact prefixLift 3614023
  have htrace : WordTrace (prefixWord ++ tailWord_3614023) baseStart_3614023 baseEnd_3614023 := by
    simpa [prefixWord, tailWord_3614023, baseEnd_3614023] using wordTrace_append hprefix tailTrace_3614023
  have hstable : (prefixWord ++ tailWord_3614023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614023).length < 2 ^ (prefixWord ++ tailWord_3614023).sum := by decide
  have hdescent : baseEnd_3614023 < baseStart_3614023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614039 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 6]
def baseStart_3614039 : Nat := 118140960795 + 3614039 * 2 ^ 59
def prefixEnd_3614039 : Nat := 4983230072969 + 3 ^ 40 * 3614039 * 2
def baseEnd_3614039 : Nat := 618579703698163596497281

theorem tailTrace_3614039 : CollatzResearch.WordTrace tailWord_3614039 prefixEnd_3614039 618579703698163596497281 := by
  unfold tailWord_3614039
  simp only [CollatzResearch.WordTrace]
  refine ⟨131814831353961406566221171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87876554235974271044147447 131814831353961406566221171)
  ·
    refine ⟨197722247030942109849331757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131814831353961406566221171 197722247030942109849331757)
    ·
      refine ⟨74145842636603291193499409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197722247030942109849331757 74145842636603291193499409)
      ·
        refine ⟨55609381977452468395124557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74145842636603291193499409 55609381977452468395124557)
        ·
          refine ⟨20853518241544675648171709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55609381977452468395124557 20853518241544675648171709)
          ·
            refine ⟨7820069340579253368064391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20853518241544675648171709 7820069340579253368064391)
            ·
              refine ⟨11730104010868880052096587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820069340579253368064391 11730104010868880052096587)
              ·
                refine ⟨17595156016303320078144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730104010868880052096587 17595156016303320078144881)
                ·
                  refine ⟨13196367012227490058608661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17595156016303320078144881 13196367012227490058608661)
                  ·
                    refine ⟨618579703698163596497281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13196367012227490058608661 618579703698163596497281)
                    ·
                      rfl

theorem cell23_3614039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_3614039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614039 prefixEnd_3614039 := by exact prefixLift 3614039
  have htrace : WordTrace (prefixWord ++ tailWord_3614039) baseStart_3614039 baseEnd_3614039 := by
    simpa [prefixWord, tailWord_3614039, baseEnd_3614039] using wordTrace_append hprefix tailTrace_3614039
  have hstable : (prefixWord ++ tailWord_3614039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614039).length < 2 ^ (prefixWord ++ tailWord_3614039).sum := by decide
  have hdescent : baseEnd_3614039 < baseStart_3614039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614136 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_3614136 : Nat := 118140960795 + 3614136 * 2 ^ 59
def prefixEnd_3614136 : Nat := 4983230072969 + 3 ^ 40 * 3614136 * 2
def baseEnd_3614136 : Nat := 1855788918717976909978897

theorem tailTrace_3614136 : CollatzResearch.WordTrace tailWord_3614136 prefixEnd_3614136 1855788918717976909978897 := by
  unfold tailWord_3614136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65909184617304996066251131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87878912823073328088334841 65909184617304996066251131)
  ·
    refine ⟨98863776925957494099376697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65909184617304996066251131 98863776925957494099376697)
    ·
      refine ⟨74147832694468120574532523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98863776925957494099376697 74147832694468120574532523)
      ·
        refine ⟨111221749041702180861798785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74147832694468120574532523 111221749041702180861798785)
        ·
          refine ⟨83416311781276635646349089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111221749041702180861798785 83416311781276635646349089)
          ·
            refine ⟨62562233835957476734761817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83416311781276635646349089 62562233835957476734761817)
            ·
              refine ⟨46921675376968107551071363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62562233835957476734761817 46921675376968107551071363)
              ·
                refine ⟨70382513065452161326607045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46921675376968107551071363 70382513065452161326607045)
                ·
                  refine ⟨13196721199772280248738821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70382513065452161326607045 13196721199772280248738821)
                  ·
                    refine ⟨2474385224957302546638529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13196721199772280248738821 2474385224957302546638529)
                    ·
                      refine ⟨1855788918717976909978897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474385224957302546638529 1855788918717976909978897)
                      ·
                        rfl

theorem cell23_3614136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_3614136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614136 prefixEnd_3614136 := by exact prefixLift 3614136
  have htrace : WordTrace (prefixWord ++ tailWord_3614136) baseStart_3614136 baseEnd_3614136 := by
    simpa [prefixWord, tailWord_3614136, baseEnd_3614136] using wordTrace_append hprefix tailTrace_3614136
  have hstable : (prefixWord ++ tailWord_3614136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614136).length < 2 ^ (prefixWord ++ tailWord_3614136).sum := by decide
  have hdescent : baseEnd_3614136 < baseStart_3614136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614173 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3614173 : Nat := 118140960795 + 3614173 * 2 ^ 59
def prefixEnd_3614173 : Nat := 4983230072969 + 3 ^ 40 * 3614173 * 2
def baseEnd_3614173 : Nat := 1855807917502193265216227

theorem tailTrace_3614173 : CollatzResearch.WordTrace tailWord_3614173 prefixEnd_3614173 1855807917502193265216227 := by
  unfold tailWord_3614173
  simp only [CollatzResearch.WordTrace]
  refine ⟨131819718735475947451599173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87879812490317298301066115 131819718735475947451599173)
  ·
    refine ⟨24716197262901740147174845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131819718735475947451599173 24716197262901740147174845)
    ·
      refine ⟨9268573973588152555190567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24716197262901740147174845 9268573973588152555190567)
      ·
        refine ⟨13902860960382228832785851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268573973588152555190567 13902860960382228832785851)
        ·
          refine ⟨20854291440573343249178777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902860960382228832785851 20854291440573343249178777)
          ·
            refine ⟨15640718580430007436884083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20854291440573343249178777 15640718580430007436884083)
            ·
              refine ⟨23461077870645011155326125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640718580430007436884083 23461077870645011155326125)
              ·
                refine ⟨8797904201491879183247297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23461077870645011155326125 8797904201491879183247297)
                ·
                  refine ⟨6598428151118909387435473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8797904201491879183247297 6598428151118909387435473)
                  ·
                    refine ⟨4948821113339182040576605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6598428151118909387435473 4948821113339182040576605)
                    ·
                      refine ⟨1855807917502193265216227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948821113339182040576605 1855807917502193265216227)
                      ·
                        rfl

theorem cell23_3614173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3614173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614173 prefixEnd_3614173 := by exact prefixLift 3614173
  have htrace : WordTrace (prefixWord ++ tailWord_3614173) baseStart_3614173 baseEnd_3614173 := by
    simpa [prefixWord, tailWord_3614173, baseEnd_3614173] using wordTrace_append hprefix tailTrace_3614173
  have hstable : (prefixWord ++ tailWord_3614173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614173).length < 2 ^ (prefixWord ++ tailWord_3614173).sum := by decide
  have hdescent : baseEnd_3614173 < baseStart_3614173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614197 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3614197 : Nat := 118140960795 + 3614197 * 2 ^ 59
def prefixEnd_3614197 : Nat := 4983230072969 + 3 ^ 40 * 3614197 * 2
def baseEnd_3614197 : Nat := 618606747012633723772039

theorem tailTrace_3614197 : CollatzResearch.WordTrace tailWord_3614197 prefixEnd_3614197 618606747012633723772039 := by
  unfold tailWord_3614197
  simp only [CollatzResearch.WordTrace]
  refine ⟨131820594087388999550472845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87880396058259333033648563 131820594087388999550472845)
  ·
    refine ⟨49432722782770874831427317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131820594087388999550472845 49432722782770874831427317)
    ·
      refine ⟨4634317760884769515446311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49432722782770874831427317 4634317760884769515446311)
      ·
        refine ⟨6951476641327154273169467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634317760884769515446311 6951476641327154273169467)
        ·
          refine ⟨10427214961990731409754201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951476641327154273169467 10427214961990731409754201)
          ·
            refine ⟨7820411221493048557315651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10427214961990731409754201 7820411221493048557315651)
            ·
              refine ⟨11730616832239572835973477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820411221493048557315651 11730616832239572835973477)
              ·
                refine ⟨2199490656044919906745027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11730616832239572835973477 2199490656044919906745027)
                ·
                  refine ⟨3299235984067379860117541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199490656044919906745027 3299235984067379860117541)
                  ·
                    refine ⟨618606747012633723772039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299235984067379860117541 618606747012633723772039)
                    ·
                      rfl

theorem cell23_3614197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3614197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614197 prefixEnd_3614197 := by exact prefixLift 3614197
  have htrace : WordTrace (prefixWord ++ tailWord_3614197) baseStart_3614197 baseEnd_3614197 := by
    simpa [prefixWord, tailWord_3614197, baseEnd_3614197] using wordTrace_append hprefix tailTrace_3614197
  have hstable : (prefixWord ++ tailWord_3614197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614197).length < 2 ^ (prefixWord ++ tailWord_3614197).sum := by decide
  have hdescent : baseEnd_3614197 < baseStart_3614197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614214 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3614214 : Nat := 118140960795 + 3614214 * 2 ^ 59
def prefixEnd_3614214 : Nat := 4983230072969 + 3 ^ 40 * 3614214 * 2
def baseEnd_3614214 : Nat := 618609656736342534934513

theorem tailTrace_3614214 : CollatzResearch.WordTrace tailWord_3614214 prefixEnd_3614214 618609656736342534934513 := by
  unfold tailWord_3614214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119412941510231607932553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87880809418884940969227797 4119412941510231607932553)
  ·
    refine ⟨3089559706132673705949415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4119412941510231607932553 3089559706132673705949415)
    ·
      refine ⟨4634339559199010558924123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089559706132673705949415 4634339559199010558924123)
      ·
        refine ⟨6951509338798515838386185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634339559199010558924123 6951509338798515838386185)
        ·
          refine ⟨5213632004098886878789639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6951509338798515838386185 5213632004098886878789639)
          ·
            refine ⟨7820448006148330318184459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213632004098886878789639 7820448006148330318184459)
            ·
              refine ⟨11730672009222495477276689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820448006148330318184459 11730672009222495477276689)
              ·
                refine ⟨8798004006916871607957517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11730672009222495477276689 8798004006916871607957517)
                ·
                  refine ⟨3299251502593826852984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8798004006916871607957517 3299251502593826852984069)
                  ·
                    refine ⟨618609656736342534934513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299251502593826852984069 618609656736342534934513)
                    ·
                      rfl

theorem cell23_3614214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3614214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614214 prefixEnd_3614214 := by exact prefixLift 3614214
  have htrace : WordTrace (prefixWord ++ tailWord_3614214) baseStart_3614214 baseEnd_3614214 := by
    simpa [prefixWord, tailWord_3614214, baseEnd_3614214] using wordTrace_append hprefix tailTrace_3614214
  have hstable : (prefixWord ++ tailWord_3614214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614214).length < 2 ^ (prefixWord ++ tailWord_3614214).sum := by decide
  have hdescent : baseEnd_3614214 < baseStart_3614214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614220 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3614220 : Nat := 118140960795 + 3614220 * 2 ^ 59
def prefixEnd_3614220 : Nat := 4983230072969 + 3 ^ 40 * 3614220 * 2
def baseEnd_3614220 : Nat := 1855832051092954581328511

theorem tailTrace_3614220 : CollatzResearch.WordTrace tailWord_3614220 prefixEnd_3614220 1855832051092954581328511 := by
  unfold tailWord_3614220
  simp only [CollatzResearch.WordTrace]
  refine ⟨65910716483152837239280057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87880955310870449652373409 65910716483152837239280057)
  ·
    refine ⟨49433037362364627929460043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65910716483152837239280057 49433037362364627929460043)
    ·
      refine ⟨74149556043546941894190065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49433037362364627929460043 74149556043546941894190065)
      ·
        refine ⟨55612167032660206420642549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74149556043546941894190065 55612167032660206420642549)
        ·
          refine ⟨5213640659311894351935239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55612167032660206420642549 5213640659311894351935239)
          ·
            refine ⟨7820460988967841527902859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213640659311894351935239 7820460988967841527902859)
            ·
              refine ⟨11730691483451762291854289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820460988967841527902859 11730691483451762291854289)
              ·
                refine ⟨8798018612588821718890717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11730691483451762291854289 8798018612588821718890717)
                ·
                  refine ⟨3299256979720808144584019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8798018612588821718890717 3299256979720808144584019)
                  ·
                    refine ⟨4948885469581212216876029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299256979720808144584019 4948885469581212216876029)
                    ·
                      refine ⟨1855832051092954581328511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948885469581212216876029 1855832051092954581328511)
                      ·
                        rfl

theorem cell23_3614220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3614220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614220 prefixEnd_3614220 := by exact prefixLift 3614220
  have htrace : WordTrace (prefixWord ++ tailWord_3614220) baseStart_3614220 baseEnd_3614220 := by
    simpa [prefixWord, tailWord_3614220, baseEnd_3614220] using wordTrace_append hprefix tailTrace_3614220
  have hstable : (prefixWord ++ tailWord_3614220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614220).length < 2 ^ (prefixWord ++ tailWord_3614220).sum := by decide
  have hdescent : baseEnd_3614220 < baseStart_3614220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614236 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3614236 : Nat := 118140960795 + 3614236 * 2 ^ 59
def prefixEnd_3614236 : Nat := 4983230072969 + 3 ^ 40 * 3614236 * 2
def baseEnd_3614236 : Nat := 618613422261142172909479

theorem tailTrace_3614236 : CollatzResearch.WordTrace tailWord_3614236 prefixEnd_3614236 618613422261142172909479 := by
  unfold tailWord_3614236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65911008267123854605571281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87881344356165139474095041 65911008267123854605571281)
  ·
    refine ⟨49433256200342890954178461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65911008267123854605571281 49433256200342890954178461)
    ·
      refine ⟨18537471075128584107816923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49433256200342890954178461 18537471075128584107816923)
      ·
        refine ⟨27806206612692876161725385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18537471075128584107816923 27806206612692876161725385)
        ·
          refine ⟨20854654959519657121294039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27806206612692876161725385 20854654959519657121294039)
          ·
            refine ⟨31281982439279485681941059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20854654959519657121294039 31281982439279485681941059)
            ·
              refine ⟨46922973658919228522911589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31281982439279485681941059 46922973658919228522911589)
              ·
                refine ⟨8798057561047355348045923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46922973658919228522911589 8798057561047355348045923)
                ·
                  refine ⟨13197086341571033022068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798057561047355348045923 13197086341571033022068885)
                  ·
                    refine ⟨618613422261142172909479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13197086341571033022068885 618613422261142172909479)
                    ·
                      rfl

theorem cell23_3614236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3614236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614236 prefixEnd_3614236 := by exact prefixLift 3614236
  have htrace : WordTrace (prefixWord ++ tailWord_3614236) baseStart_3614236 baseEnd_3614236 := by
    simpa [prefixWord, tailWord_3614236, baseEnd_3614236] using wordTrace_append hprefix tailTrace_3614236
  have hstable : (prefixWord ++ tailWord_3614236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614236).length < 2 ^ (prefixWord ++ tailWord_3614236).sum := by decide
  have hdescent : baseEnd_3614236 < baseStart_3614236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614237 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_3614237 : Nat := 118140960795 + 3614237 * 2 ^ 59
def prefixEnd_3614237 : Nat := 4983230072969 + 3 ^ 40 * 3614237 * 2
def baseEnd_3614237 : Nat := 1855840780264081014815933

theorem tailTrace_3614237 : CollatzResearch.WordTrace tailWord_3614237 prefixEnd_3614237 1855840780264081014815933 := by
  unfold tailWord_3614237
  simp only [CollatzResearch.WordTrace]
  refine ⟨131822053007244086381928965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87881368671496057587952643 131822053007244086381928965)
  ·
    refine ⟨24716634938858266196611681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131822053007244086381928965 24716634938858266196611681)
    ·
      refine ⟨18537476204143699647458761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24716634938858266196611681 18537476204143699647458761)
      ·
        refine ⟨13903107153107774735594071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18537476204143699647458761 13903107153107774735594071)
        ·
          refine ⟨20854660729661662103391107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903107153107774735594071 20854660729661662103391107)
          ·
            refine ⟨31281991094492493155086661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20854660729661662103391107 31281991094492493155086661)
            ·
              refine ⟨5865373330217342466578749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31281991094492493155086661 5865373330217342466578749)
              ·
                refine ⟨2199514998831503424967031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5865373330217342466578749 2199514998831503424967031)
                ·
                  refine ⟨3299272498247255137450547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199514998831503424967031 3299272498247255137450547)
                  ·
                    refine ⟨4948908747370882706175821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299272498247255137450547 4948908747370882706175821)
                    ·
                      refine ⟨1855840780264081014815933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4948908747370882706175821 1855840780264081014815933)
                      ·
                        rfl

theorem cell23_3614237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_3614237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614237 prefixEnd_3614237 := by exact prefixLift 3614237
  have htrace : WordTrace (prefixWord ++ tailWord_3614237) baseStart_3614237 baseEnd_3614237 := by
    simpa [prefixWord, tailWord_3614237, baseEnd_3614237] using wordTrace_append hprefix tailTrace_3614237
  have hstable : (prefixWord ++ tailWord_3614237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614237).length < 2 ^ (prefixWord ++ tailWord_3614237).sum := by decide
  have hdescent : baseEnd_3614237 < baseStart_3614237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614240 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_3614240 : Nat := 118140960795 + 3614240 * 2 ^ 59
def prefixEnd_3614240 : Nat := 4983230072969 + 3 ^ 40 * 3614240 * 2
def baseEnd_3614240 : Nat := 618614106902014834359473

theorem tailTrace_3614240 : CollatzResearch.WordTrace tailWord_3614240 prefixEnd_3614240 618614106902014834359473 := by
  unfold tailWord_3614240
  simp only [CollatzResearch.WordTrace]
  refine ⟨65911081213116608947144087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87881441617488811929525449 65911081213116608947144087)
  ·
    refine ⟨98866621819674913420716131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65911081213116608947144087 98866621819674913420716131)
    ·
      refine ⟨148299932729512370131074197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98866621819674913420716131 148299932729512370131074197)
      ·
        refine ⟨6951559346695892349894103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148299932729512370131074197 6951559346695892349894103)
        ·
          refine ⟨10427339020043838524841155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951559346695892349894103 10427339020043838524841155)
          ·
            refine ⟨15641008530065757787261733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427339020043838524841155 15641008530065757787261733)
            ·
              refine ⟨2932689099387329585111575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15641008530065757787261733 2932689099387329585111575)
              ·
                refine ⟨4399033649080994377667363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932689099387329585111575 4399033649080994377667363)
                ·
                  refine ⟨6598550473621491566501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399033649080994377667363 6598550473621491566501045)
                  ·
                    refine ⟨618614106902014834359473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6598550473621491566501045 618614106902014834359473)
                    ·
                      rfl

theorem cell23_3614240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_3614240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614240 prefixEnd_3614240 := by exact prefixLift 3614240
  have htrace : WordTrace (prefixWord ++ tailWord_3614240) baseStart_3614240 baseEnd_3614240 := by
    simpa [prefixWord, tailWord_3614240, baseEnd_3614240] using wordTrace_append hprefix tailTrace_3614240
  have hstable : (prefixWord ++ tailWord_3614240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614240).length < 2 ^ (prefixWord ++ tailWord_3614240).sum := by decide
  have hdescent : baseEnd_3614240 < baseStart_3614240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614303 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 7, 3, 2]
def baseStart_3614303 : Nat := 118140960795 + 3614303 * 2 ^ 59
def prefixEnd_3614303 : Nat := 4983230072969 + 3 ^ 40 * 3614303 * 2
def baseEnd_3614303 : Nat := 1855874669987277756590629

theorem tailTrace_3614303 : CollatzResearch.WordTrace tailWord_3614303 prefixEnd_3614303 1855874669987277756590629 := by
  unfold tailWord_3614303
  simp only [CollatzResearch.WordTrace]
  refine ⟨131824460225004979653831563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87882973483336653102554375 131824460225004979653831563)
  ·
    refine ⟨197736690337507469480747345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131824460225004979653831563 197736690337507469480747345)
    ·
      refine ⟨148302517753130602110560509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197736690337507469480747345 148302517753130602110560509)
      ·
        refine ⟨55613444157423975791460191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148302517753130602110560509 55613444157423975791460191)
        ·
          refine ⟨83420166236135963687190287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55613444157423975791460191 83420166236135963687190287)
          ·
            refine ⟨125130249354203945530785431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83420166236135963687190287 125130249354203945530785431)
            ·
              refine ⟨187695374031305918296178147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125130249354203945530785431 187695374031305918296178147)
              ·
                refine ⟨281543061046958877444267221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187695374031305918296178147 281543061046958877444267221)
                ·
                  refine ⟨6598665493288098690100013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281543061046958877444267221 6598665493288098690100013)
                  ·
                    refine ⟨2474499559983037008787505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6598665493288098690100013 2474499559983037008787505)
                    ·
                      refine ⟨1855874669987277756590629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474499559983037008787505 1855874669987277756590629)
                      ·
                        rfl

theorem cell23_3614303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_3614303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614303 prefixEnd_3614303 := by exact prefixLift 3614303
  have htrace : WordTrace (prefixWord ++ tailWord_3614303) baseStart_3614303 baseEnd_3614303 := by
    simpa [prefixWord, tailWord_3614303, baseEnd_3614303] using wordTrace_append hprefix tailTrace_3614303
  have hstable : (prefixWord ++ tailWord_3614303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614303).length < 2 ^ (prefixWord ++ tailWord_3614303).sum := by decide
  have hdescent : baseEnd_3614303 < baseStart_3614303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614316 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_3614316 : Nat := 118140960795 + 3614316 * 2 ^ 59
def prefixEnd_3614316 : Nat := 4983230072969 + 3 ^ 40 * 3614316 * 2
def baseEnd_3614316 : Nat := 1855881345235786205728069

theorem tailTrace_3614316 : CollatzResearch.WordTrace tailWord_3614316 prefixEnd_3614316 1855881345235786205728069 := by
  unfold tailWord_3614316
  simp only [CollatzResearch.WordTrace]
  refine ⟨65912467186978941437027401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87883289582638588582703201 65912467186978941437027401)
  ·
    refine ⟨49434350390234206077770551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65912467186978941437027401 49434350390234206077770551)
    ·
      refine ⟨74151525585351309116655827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49434350390234206077770551 74151525585351309116655827)
      ·
        refine ⟨111227288378026963674983741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74151525585351309116655827 111227288378026963674983741)
        ·
          refine ⟨41710233141760111378118903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111227288378026963674983741 41710233141760111378118903)
          ·
            refine ⟨62565349712640167067178355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41710233141760111378118903 62565349712640167067178355)
            ·
              refine ⟨93848024568960250600767533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62565349712640167067178355 93848024568960250600767533)
              ·
                refine ⟨35193009213360093975287825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93848024568960250600767533 35193009213360093975287825)
                ·
                  refine ⟨26394756910020070481465869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35193009213360093975287825 26394756910020070481465869)
                  ·
                    refine ⟨9898033841257526430549701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26394756910020070481465869 9898033841257526430549701)
                    ·
                      refine ⟨1855881345235786205728069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9898033841257526430549701 1855881345235786205728069)
                      ·
                        rfl

theorem cell23_3614316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_3614316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614316 prefixEnd_3614316 := by exact prefixLift 3614316
  have htrace : WordTrace (prefixWord ++ tailWord_3614316) baseStart_3614316 baseEnd_3614316 := by
    simpa [prefixWord, tailWord_3614316, baseEnd_3614316] using wordTrace_append hprefix tailTrace_3614316
  have hstable : (prefixWord ++ tailWord_3614316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614316).length < 2 ^ (prefixWord ++ tailWord_3614316).sum := by decide
  have hdescent : baseEnd_3614316 < baseStart_3614316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614336 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_3614336 : Nat := 118140960795 + 3614336 * 2 ^ 59
def prefixEnd_3614336 : Nat := 4983230072969 + 3 ^ 40 * 3614336 * 2
def baseEnd_3614336 : Nat := 1855891614848876127477977

theorem tailTrace_3614336 : CollatzResearch.WordTrace tailWord_3614336 prefixEnd_3614336 1855891614848876127477977 := by
  unfold tailWord_3614336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65912831916942713144891431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87883775889256950859855241 65912831916942713144891431)
  ·
    refine ⟨98869247875414069717337147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65912831916942713144891431 98869247875414069717337147)
    ·
      refine ⟨148303871813121104576005721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98869247875414069717337147 148303871813121104576005721)
      ·
        refine ⟨111227903859840828432004291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148303871813121104576005721 111227903859840828432004291)
        ·
          refine ⟨166841855789761242648006437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111227903859840828432004291 166841855789761242648006437)
          ·
            refine ⟨31282847960580232996501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166841855789761242648006437 31282847960580232996501207)
            ·
              refine ⟨46924271940870349494751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31282847960580232996501207 46924271940870349494751811)
              ·
                refine ⟨70386407911305524242127717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46924271940870349494751811 70386407911305524242127717)
                ·
                  refine ⟨13197451483369785795398947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70386407911305524242127717 13197451483369785795398947)
                  ·
                    refine ⟨19796177225054678693098421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13197451483369785795398947 19796177225054678693098421)
                    ·
                      refine ⟨1855891614848876127477977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19796177225054678693098421 1855891614848876127477977)
                      ·
                        rfl

theorem cell23_3614336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_3614336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614336 prefixEnd_3614336 := by exact prefixLift 3614336
  have htrace : WordTrace (prefixWord ++ tailWord_3614336) baseStart_3614336 baseEnd_3614336 := by
    simpa [prefixWord, tailWord_3614336, baseEnd_3614336] using wordTrace_append hprefix tailTrace_3614336
  have hstable : (prefixWord ++ tailWord_3614336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614336).length < 2 ^ (prefixWord ++ tailWord_3614336).sum := by decide
  have hdescent : baseEnd_3614336 < baseStart_3614336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614337 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_3614337 : Nat := 118140960795 + 3614337 * 2 ^ 59
def prefixEnd_3614337 : Nat := 4983230072969 + 3 ^ 40 * 3614337 * 2
def baseEnd_3614337 : Nat := 1855892128329530623565473

theorem tailTrace_3614337 : CollatzResearch.WordTrace tailWord_3614337 prefixEnd_3614337 1855892128329530623565473 := by
  unfold tailWord_3614337
  simp only [CollatzResearch.WordTrace]
  refine ⟨131825700306881803460569265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87883800204587868973712843 131825700306881803460569265)
  ·
    refine ⟨98869275230161352595426949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131825700306881803460569265 98869275230161352595426949)
    ·
      refine ⟨18537989105655253611642553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98869275230161352595426949 18537989105655253611642553)
      ·
        refine ⟨13903491829241440208731915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18537989105655253611642553 13903491829241440208731915)
        ·
          refine ⟨20855237743862160313097873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903491829241440208731915 20855237743862160313097873)
          ·
            refine ⟨15641428307896620234823405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855237743862160313097873 15641428307896620234823405)
            ·
              refine ⟨5865535615461232588058777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15641428307896620234823405 5865535615461232588058777)
              ·
                refine ⟨4399151711595924441044083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865535615461232588058777 4399151711595924441044083)
                ·
                  refine ⟨6598727567393886661566125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399151711595924441044083 6598727567393886661566125)
                  ·
                    refine ⟨2474522837772707498087297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6598727567393886661566125 2474522837772707498087297)
                    ·
                      refine ⟨1855892128329530623565473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474522837772707498087297 1855892128329530623565473)
                      ·
                        rfl

theorem cell23_3614337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_3614337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614337 prefixEnd_3614337 := by exact prefixLift 3614337
  have htrace : WordTrace (prefixWord ++ tailWord_3614337) baseStart_3614337 baseEnd_3614337 := by
    simpa [prefixWord, tailWord_3614337, baseEnd_3614337] using wordTrace_append hprefix tailTrace_3614337
  have hstable : (prefixWord ++ tailWord_3614337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614337).length < 2 ^ (prefixWord ++ tailWord_3614337).sum := by decide
  have hdescent : baseEnd_3614337 < baseStart_3614337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614350 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3614350 : Nat := 118140960795 + 3614350 * 2 ^ 59
def prefixEnd_3614350 : Nat := 4983230072969 + 3 ^ 40 * 3614350 * 2
def baseEnd_3614350 : Nat := 1855898803578039072702913

theorem tailTrace_3614350 : CollatzResearch.WordTrace tailWord_3614350 prefixEnd_3614350 1855898803578039072702913 := by
  unfold tailWord_3614350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16478271806979338335099063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87884116303889804453861669 16478271806979338335099063)
  ·
    refine ⟨24717407710469007502648595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16478271806979338335099063 24717407710469007502648595)
    ·
      refine ⟨37076111565703511253972893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24717407710469007502648595 37076111565703511253972893)
      ·
        refine ⟨13903541837138816720239835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37076111565703511253972893 13903541837138816720239835)
        ·
          refine ⟨20855312755708225080359753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903541837138816720239835 20855312755708225080359753)
          ·
            refine ⟨15641484566781168810269815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855312755708225080359753 15641484566781168810269815)
            ·
              refine ⟨23462226850171753215404723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641484566781168810269815 23462226850171753215404723)
              ·
                refine ⟨35193340275257629823107085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462226850171753215404723 35193340275257629823107085)
                ·
                  refine ⟨13197502603221611183665157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35193340275257629823107085 13197502603221611183665157)
                  ·
                    refine ⟨2474531738104052096937217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13197502603221611183665157 2474531738104052096937217)
                    ·
                      refine ⟨1855898803578039072702913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474531738104052096937217 1855898803578039072702913)
                      ·
                        rfl

theorem cell23_3614350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3614350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614350 prefixEnd_3614350 := by exact prefixLift 3614350
  have htrace : WordTrace (prefixWord ++ tailWord_3614350) baseStart_3614350 baseEnd_3614350 := by
    simpa [prefixWord, tailWord_3614350, baseEnd_3614350] using wordTrace_append hprefix tailTrace_3614350
  have hstable : (prefixWord ++ tailWord_3614350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614350).length < 2 ^ (prefixWord ++ tailWord_3614350).sum := by decide
  have hdescent : baseEnd_3614350 < baseStart_3614350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614383 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_3614383 : Nat := 118140960795 + 3614383 * 2 ^ 59
def prefixEnd_3614383 : Nat := 4983230072969 + 3 ^ 40 * 3614383 * 2
def baseEnd_3614383 : Nat := 1855915748439637443590261

theorem tailTrace_3614383 : CollatzResearch.WordTrace tailWord_3614383 prefixEnd_3614383 1855915748439637443590261 := by
  unfold tailWord_3614383
  simp only [CollatzResearch.WordTrace]
  refine ⟨131827378064715153316743803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87884918709810102211162535 131827378064715153316743803)
  ·
    refine ⟨197741067097072729975115705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131827378064715153316743803 197741067097072729975115705)
    ·
      refine ⟨148305800322804547481336779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197741067097072729975115705 148305800322804547481336779)
      ·
        refine ⟨222458700484206821222005169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148305800322804547481336779 222458700484206821222005169)
        ·
          refine ⟨166844025363155115916503877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222458700484206821222005169 166844025363155115916503877)
          ·
            refine ⟨31283254755591584234344477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166844025363155115916503877 31283254755591584234344477)
            ·
              refine ⟨11731220533346844087879179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31283254755591584234344477 11731220533346844087879179)
              ·
                refine ⟨17596830800020266131818769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731220533346844087879179 17596830800020266131818769)
                ·
                  refine ⟨13197623100015199598864077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17596830800020266131818769 13197623100015199598864077)
                  ·
                    refine ⟨4949108662505699849574029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13197623100015199598864077 4949108662505699849574029)
                    ·
                      refine ⟨1855915748439637443590261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949108662505699849574029 1855915748439637443590261)
                      ·
                        rfl

theorem cell23_3614383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_3614383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614383 prefixEnd_3614383 := by exact prefixLift 3614383
  have htrace : WordTrace (prefixWord ++ tailWord_3614383) baseStart_3614383 baseEnd_3614383 := by
    simpa [prefixWord, tailWord_3614383, baseEnd_3614383] using wordTrace_append hprefix tailTrace_3614383
  have hstable : (prefixWord ++ tailWord_3614383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614383).length < 2 ^ (prefixWord ++ tailWord_3614383).sum := by decide
  have hdescent : baseEnd_3614383 < baseStart_3614383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614390 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_3614390 : Nat := 118140960795 + 3614390 * 2 ^ 59
def prefixEnd_3614390 : Nat := 4983230072969 + 3 ^ 40 * 3614390 * 2
def baseEnd_3614390 : Nat := 206213260311579879578081

theorem tailTrace_3614390 : CollatzResearch.WordTrace tailWord_3614390 prefixEnd_3614390 206213260311579879578081 := by
  unfold tailWord_3614390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239227085980612094515539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87885088917126529008165749 8239227085980612094515539)
  ·
    refine ⟨12358840628970918141773309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239227085980612094515539 12358840628970918141773309)
    ·
      refine ⟨4634565235864094303164991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12358840628970918141773309 4634565235864094303164991)
      ·
        refine ⟨6951847853796141454747487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634565235864094303164991 6951847853796141454747487)
        ·
          refine ⟨10427771780694212182121231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951847853796141454747487 10427771780694212182121231)
          ·
            refine ⟨15641657671041318273181847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427771780694212182121231 15641657671041318273181847)
            ·
              refine ⟨23462486506561977409772771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641657671041318273181847 23462486506561977409772771)
              ·
                refine ⟨35193729759842966114659157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462486506561977409772771 35193729759842966114659157)
                ·
                  refine ⟨206213260311579879578081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35193729759842966114659157 206213260311579879578081)
                  ·
                    rfl

theorem cell23_3614390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_3614390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614390 prefixEnd_3614390 := by exact prefixLift 3614390
  have htrace : WordTrace (prefixWord ++ tailWord_3614390) baseStart_3614390 baseEnd_3614390 := by
    simpa [prefixWord, tailWord_3614390, baseEnd_3614390] using wordTrace_append hprefix tailTrace_3614390
  have hstable : (prefixWord ++ tailWord_3614390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614390).length < 2 ^ (prefixWord ++ tailWord_3614390).sum := by decide
  have hdescent : baseEnd_3614390 < baseStart_3614390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614423 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_3614423 : Nat := 118140960795 + 3614423 * 2 ^ 59
def prefixEnd_3614423 : Nat := 4983230072969 + 3 ^ 40 * 3614423 * 2
def baseEnd_3614423 : Nat := 1855936287665817287090077

theorem tailTrace_3614423 : CollatzResearch.WordTrace tailWord_3614423 prefixEnd_3614423 1855936287665817287090077 := by
  unfold tailWord_3614423
  simp only [CollatzResearch.WordTrace]
  refine ⟨131828836984570240148199923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87885891323046826765466615 131828836984570240148199923)
  ·
    refine ⟨197743255476855360222299885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131828836984570240148199923 197743255476855360222299885)
    ·
      refine ⟨74153720803820760083362457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197743255476855360222299885 74153720803820760083362457)
      ·
        refine ⟨55615290602865570062521843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74153720803820760083362457 55615290602865570062521843)
        ·
          refine ⟨83422935904298355093782765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55615290602865570062521843 83422935904298355093782765)
          ·
            refine ⟨31283600964111883160168537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83422935904298355093782765 31283600964111883160168537)
            ·
              refine ⟨23462700723083912370126403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31283600964111883160168537 23462700723083912370126403)
              ·
                refine ⟨35194051084625868555189605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462700723083912370126403 35194051084625868555189605)
                ·
                  refine ⟨6598884578367350354098051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35194051084625868555189605 6598884578367350354098051)
                  ·
                    refine ⟨9898326867551025531147077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598884578367350354098051 9898326867551025531147077)
                    ·
                      refine ⟨1855936287665817287090077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9898326867551025531147077 1855936287665817287090077)
                      ·
                        rfl

theorem cell23_3614423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_3614423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614423 prefixEnd_3614423 := by exact prefixLift 3614423
  have htrace : WordTrace (prefixWord ++ tailWord_3614423) baseStart_3614423 baseEnd_3614423 := by
    simpa [prefixWord, tailWord_3614423, baseEnd_3614423] using wordTrace_append hprefix tailTrace_3614423
  have hstable : (prefixWord ++ tailWord_3614423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614423).length < 2 ^ (prefixWord ++ tailWord_3614423).sum := by decide
  have hdescent : baseEnd_3614423 < baseStart_3614423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614443 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3]
def baseStart_3614443 : Nat := 118140960795 + 3614443 * 2 ^ 59
def prefixEnd_3614443 : Nat := 4983230072969 + 3 ^ 40 * 3614443 * 2
def baseEnd_3614443 : Nat := 1855946557278907208839985

theorem tailTrace_3614443 : CollatzResearch.WordTrace tailWord_3614443 prefixEnd_3614443 1855946557278907208839985 := by
  unfold tailWord_3614443
  simp only [CollatzResearch.WordTrace]
  refine ⟨131829566444497783563927983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87886377629665189042618655 131829566444497783563927983)
  ·
    refine ⟨197744349666746675345891975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131829566444497783563927983 197744349666746675345891975)
    ·
      refine ⟨296616524500120013018837963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197744349666746675345891975 296616524500120013018837963)
      ·
        refine ⟨444924786750180019528256945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296616524500120013018837963 444924786750180019528256945)
        ·
          refine ⟨333693590062635014646192709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444924786750180019528256945 333693590062635014646192709)
          ·
            refine ⟨62567548136744065246161133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333693590062635014646192709 62567548136744065246161133)
            ·
              refine ⟨23462830551279024467310425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62567548136744065246161133 23462830551279024467310425)
              ·
                refine ⟨17597122913459268350482819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23462830551279024467310425 17597122913459268350482819)
                ·
                  refine ⟨26395684370188902525724229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17597122913459268350482819 26395684370188902525724229)
                  ·
                    refine ⟨4949190819410419223573293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26395684370188902525724229 4949190819410419223573293)
                    ·
                      refine ⟨1855946557278907208839985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949190819410419223573293 1855946557278907208839985)
                      ·
                        rfl

theorem cell23_3614443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].length) (baseStart_3614443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614443 prefixEnd_3614443 := by exact prefixLift 3614443
  have htrace : WordTrace (prefixWord ++ tailWord_3614443) baseStart_3614443 baseEnd_3614443 := by
    simpa [prefixWord, tailWord_3614443, baseEnd_3614443] using wordTrace_append hprefix tailTrace_3614443
  have hstable : (prefixWord ++ tailWord_3614443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614443).length < 2 ^ (prefixWord ++ tailWord_3614443).sum := by decide
  have hdescent : baseEnd_3614443 < baseStart_3614443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614450 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3614450 : Nat := 118140960795 + 3614450 * 2 ^ 59
def prefixEnd_3614450 : Nat := 4983230072969 + 3 ^ 40 * 3614450 * 2
def baseEnd_3614450 : Nat := 618650050547829560484151

theorem tailTrace_3614450 : CollatzResearch.WordTrace tailWord_3614450 prefixEnd_3614450 618650050547829560484151 := by
  unfold tailWord_3614450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957455438868105939858201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87886547836981615839621869 32957455438868105939858201)
  ·
    refine ⟨24718091579151079454893651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957455438868105939858201 24718091579151079454893651)
    ·
      refine ⟨37077137368726619182340477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24718091579151079454893651 37077137368726619182340477)
      ·
        refine ⟨13903926513272482193377679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37077137368726619182340477 13903926513272482193377679)
        ·
          refine ⟨20855889769908723290066519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903926513272482193377679 20855889769908723290066519)
          ·
            refine ⟨31283834654863084935099779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20855889769908723290066519 31283834654863084935099779)
            ·
              refine ⟨46925751982294627402649669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31283834654863084935099779 46925751982294627402649669)
              ·
                refine ⟨8798578496680242637996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46925751982294627402649669 8798578496680242637996813)
                ·
                  refine ⟨3299466936255090989248805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8798578496680242637996813 3299466936255090989248805)
                  ·
                    refine ⟨618650050547829560484151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299466936255090989248805 618650050547829560484151)
                    ·
                      rfl

theorem cell23_3614450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3614450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614450 prefixEnd_3614450 := by exact prefixLift 3614450
  have htrace : WordTrace (prefixWord ++ tailWord_3614450) baseStart_3614450 baseEnd_3614450 := by
    simpa [prefixWord, tailWord_3614450, baseEnd_3614450] using wordTrace_append hprefix tailTrace_3614450
  have hstable : (prefixWord ++ tailWord_3614450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614450).length < 2 ^ (prefixWord ++ tailWord_3614450).sum := by decide
  have hdescent : baseEnd_3614450 < baseStart_3614450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614460 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3614460 : Nat := 118140960795 + 3614460 * 2 ^ 59
def prefixEnd_3614460 : Nat := 4983230072969 + 3 ^ 40 * 3614460 * 2
def baseEnd_3614460 : Nat := 1855955286450033642327407

theorem tailTrace_3614460 : CollatzResearch.WordTrace tailWord_3614460 prefixEnd_3614460 1855955286450033642327407 := by
  unfold tailWord_3614460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65915093242718097733648417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87886790990290796978197889 65915093242718097733648417)
  ·
    refine ⟨49436319932038573300236313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65915093242718097733648417 49436319932038573300236313)
    ·
      refine ⟨37077239949028929975177235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49436319932038573300236313 37077239949028929975177235)
      ·
        refine ⟨55615859923543394962765853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37077239949028929975177235 55615859923543394962765853)
        ·
          refine ⟨20855947471328773111037195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55615859923543394962765853 20855947471328773111037195)
          ·
            refine ⟨31283921206993159666555793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20855947471328773111037195 31283921206993159666555793)
            ·
              refine ⟨23462940905244869749916845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31283921206993159666555793 23462940905244869749916845)
              ·
                refine ⟨8798602839466826156218817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23462940905244869749916845 8798602839466826156218817)
                ·
                  refine ⟨6598952129600119617164113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798602839466826156218817 6598952129600119617164113)
                  ·
                    refine ⟨4949214097200089712873085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6598952129600119617164113 4949214097200089712873085)
                    ·
                      refine ⟨1855955286450033642327407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949214097200089712873085 1855955286450033642327407)
                      ·
                        rfl

theorem cell23_3614460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3614460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614460 prefixEnd_3614460 := by exact prefixLift 3614460
  have htrace : WordTrace (prefixWord ++ tailWord_3614460) baseStart_3614460 baseEnd_3614460 := by
    simpa [prefixWord, tailWord_3614460, baseEnd_3614460] using wordTrace_append hprefix tailTrace_3614460
  have hstable : (prefixWord ++ tailWord_3614460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614460).length < 2 ^ (prefixWord ++ tailWord_3614460).sum := by decide
  have hdescent : baseEnd_3614460 < baseStart_3614460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614467 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 1, 4]
def baseStart_3614467 : Nat := 118140960795 + 3614467 * 2 ^ 59
def prefixEnd_3614467 : Nat := 4983230072969 + 3 ^ 40 * 3614467 * 2
def baseEnd_3614467 : Nat := 618652960271538371646625

theorem tailTrace_3614467 : CollatzResearch.WordTrace tailWord_3614467 prefixEnd_3614467 618652960271538371646625 := by
  unfold tailWord_3614467
  simp only [CollatzResearch.WordTrace]
  refine ⟨131830441796410835662801655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87886961197607223775201103 131830441796410835662801655)
  ·
    refine ⟨197745662694616253494202483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131830441796410835662801655 197745662694616253494202483)
    ·
      refine ⟨296618494041924380241303725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197745662694616253494202483 296618494041924380241303725)
      ·
        refine ⟨111231935265721642590488897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296618494041924380241303725 111231935265721642590488897)
        ·
          refine ⟨83423951449291231942866673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111231935265721642590488897 83423951449291231942866673)
          ·
            refine ⟨62567963586968423957150005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83423951449291231942866673 62567963586968423957150005)
            ·
              refine ⟨5865746586278289745982813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62567963586968423957150005 5865746586278289745982813)
              ·
                refine ⟨2199654969854358654743555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5865746586278289745982813 2199654969854358654743555)
                ·
                  refine ⟨3299482454781537982115333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199654969854358654743555 3299482454781537982115333)
                  ·
                    refine ⟨618652960271538371646625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299482454781537982115333 618652960271538371646625)
                    ·
                      rfl

theorem cell23_3614467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 4].length) (baseStart_3614467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614467 prefixEnd_3614467 := by exact prefixLift 3614467
  have htrace : WordTrace (prefixWord ++ tailWord_3614467) baseStart_3614467 baseEnd_3614467 := by
    simpa [prefixWord, tailWord_3614467, baseEnd_3614467] using wordTrace_append hprefix tailTrace_3614467
  have hstable : (prefixWord ++ tailWord_3614467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614467).length < 2 ^ (prefixWord ++ tailWord_3614467).sum := by decide
  have hdescent : baseEnd_3614467 < baseStart_3614467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614497 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 6]
def baseStart_3614497 : Nat := 118140960795 + 3614497 * 2 ^ 59
def prefixEnd_3614497 : Nat := 4983230072969 + 3 ^ 40 * 3614497 * 2
def baseEnd_3614497 : Nat := 206219365026027777507193

theorem tailTrace_3614497 : CollatzResearch.WordTrace tailWord_3614497 prefixEnd_3614497 206219365026027777507193 := by
  unfold tailWord_3614497
  simp only [CollatzResearch.WordTrace]
  refine ⟨131831535986302150786393745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87887690657534767190929163 131831535986302150786393745)
  ·
    refine ⟨98873651989726613089795309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131831535986302150786393745 98873651989726613089795309)
    ·
      refine ⟨37077619496147479908673241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98873651989726613089795309 37077619496147479908673241)
      ·
        refine ⟨27808214622110609931504931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37077619496147479908673241 27808214622110609931504931)
        ·
          refine ⟨41712321933165914897257397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27808214622110609931504931 41712321933165914897257397)
          ·
            refine ⟨3910530181234304521617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41712321933165914897257397 3910530181234304521617881)
            ·
              refine ⟨2932897635925728391213411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910530181234304521617881 2932897635925728391213411)
              ·
                refine ⟨4399346453888592586820117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932897635925728391213411 4399346453888592586820117)
                ·
                  refine ⟨206219365026027777507193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4399346453888592586820117 206219365026027777507193)
                  ·
                    rfl

theorem cell23_3614497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_3614497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614497 prefixEnd_3614497 := by exact prefixLift 3614497
  have htrace : WordTrace (prefixWord ++ tailWord_3614497) baseStart_3614497 baseEnd_3614497 := by
    simpa [prefixWord, tailWord_3614497, baseEnd_3614497] using wordTrace_append hprefix tailTrace_3614497
  have hstable : (prefixWord ++ tailWord_3614497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614497).length < 2 ^ (prefixWord ++ tailWord_3614497).sum := by decide
  have hdescent : baseEnd_3614497 < baseStart_3614497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614560 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_3614560 : Nat := 118140960795 + 3614560 * 2 ^ 59
def prefixEnd_3614560 : Nat := 4983230072969 + 3 ^ 40 * 3614560 * 2
def baseEnd_3614560 : Nat := 1856006634515483251076947

theorem tailTrace_3614560 : CollatzResearch.WordTrace tailWord_3614560 prefixEnd_3614560 1856006634515483251076947 := by
  unfold tailWord_3614560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65916916892536956272968567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87889222523382608363958089 65916916892536956272968567)
  ·
    refine ⟨98875375338805434409452851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65916916892536956272968567 98875375338805434409452851)
    ·
      refine ⟨148313063008208151614179277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98875375338805434409452851 148313063008208151614179277)
      ·
        refine ⟨55617398628078056855317229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148313063008208151614179277 55617398628078056855317229)
        ·
          refine ⟨20856524485529271320743961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55617398628078056855317229 20856524485529271320743961)
          ·
            refine ⟨15642393364146953490557971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20856524485529271320743961 15642393364146953490557971)
            ·
              refine ⟨23463590046220430235836957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15642393364146953490557971 23463590046220430235836957)
              ·
                refine ⟨8798846267332661338438859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23463590046220430235836957 8798846267332661338438859)
                ·
                  refine ⟨13198269400998992007658289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798846267332661338438859 13198269400998992007658289)
                  ·
                    refine ⟨9898702050749244005743717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13198269400998992007658289 9898702050749244005743717)
                    ·
                      refine ⟨1856006634515483251076947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9898702050749244005743717 1856006634515483251076947)
                      ·
                        rfl

theorem cell23_3614560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_3614560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614560 prefixEnd_3614560 := by exact prefixLift 3614560
  have htrace : WordTrace (prefixWord ++ tailWord_3614560) baseStart_3614560 baseEnd_3614560 := by
    simpa [prefixWord, tailWord_3614560, baseEnd_3614560] using wordTrace_append hprefix tailTrace_3614560
  have hstable : (prefixWord ++ tailWord_3614560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614560).length < 2 ^ (prefixWord ++ tailWord_3614560).sum := by decide
  have hdescent : baseEnd_3614560 < baseStart_3614560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614567 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3614567 : Nat := 118140960795 + 3614567 * 2 ^ 59
def prefixEnd_3614567 : Nat := 4983230072969 + 3 ^ 40 * 3614567 * 2
def baseEnd_3614567 : Nat := 1856010228880064723689415

theorem tailTrace_3614567 : CollatzResearch.WordTrace tailWord_3614567 prefixEnd_3614567 1856010228880064723689415 := by
  unfold tailWord_3614567
  simp only [CollatzResearch.WordTrace]
  refine ⟨131834089096048552741441955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87889392730699035160961303 131834089096048552741441955)
  ·
    refine ⟨197751133644072829112162933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131834089096048552741441955 197751133644072829112162933)
    ·
      refine ⟨18539168779131827729265275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197751133644072829112162933 18539168779131827729265275)
      ·
        refine ⟨27808753168697741593897913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18539168779131827729265275 27808753168697741593897913)
        ·
          refine ⟨20856564876523306195423435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27808753168697741593897913 20856564876523306195423435)
          ·
            refine ⟨31284847314784959293135153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20856564876523306195423435 31284847314784959293135153)
            ·
              refine ⟨23463635486088719469851365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31284847314784959293135153 23463635486088719469851365)
              ·
                refine ⟨4399431653641634900597131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23463635486088719469851365 4399431653641634900597131)
                ·
                  refine ⟨6599147480462452350895697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399431653641634900597131 6599147480462452350895697)
                  ·
                    refine ⟨4949360610346839263171773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599147480462452350895697 4949360610346839263171773)
                    ·
                      refine ⟨1856010228880064723689415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949360610346839263171773 1856010228880064723689415)
                      ·
                        rfl

theorem cell23_3614567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3614567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614567 prefixEnd_3614567 := by exact prefixLift 3614567
  have htrace : WordTrace (prefixWord ++ tailWord_3614567) baseStart_3614567 baseEnd_3614567 := by
    simpa [prefixWord, tailWord_3614567, baseEnd_3614567] using wordTrace_append hprefix tailTrace_3614567
  have hstable : (prefixWord ++ tailWord_3614567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614567).length < 2 ^ (prefixWord ++ tailWord_3614567).sum := by decide
  have hdescent : baseEnd_3614567 < baseStart_3614567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614597 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_3614597 : Nat := 118140960795 + 3614597 * 2 ^ 59
def prefixEnd_3614597 : Nat := 4983230072969 + 3 ^ 40 * 3614597 * 2
def baseEnd_3614597 : Nat := 1856025633299699606314277

theorem tailTrace_3614597 : CollatzResearch.WordTrace tailWord_3614597 prefixEnd_3614597 1856025633299699606314277 := by
  unfold tailWord_3614597
  simp only [CollatzResearch.WordTrace]
  refine ⟨131835183285939867865034045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87890122190626578576689363 131835183285939867865034045)
  ·
    refine ⟨49438193732227450449387767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131835183285939867865034045 49438193732227450449387767)
    ·
      refine ⟨74157290598341175674081651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49438193732227450449387767 74157290598341175674081651)
      ·
        refine ⟨111235935897511763511122477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74157290598341175674081651 111235935897511763511122477)
        ·
          refine ⟨41713475961566911316670929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111235935897511763511122477 41713475961566911316670929)
          ·
            refine ⟨31285106971175183487503197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41713475961566911316670929 31285106971175183487503197)
            ·
              refine ⟨11731915114190693807813699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31285106971175183487503197 11731915114190693807813699)
              ·
                refine ⟨17597872671286040711720549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731915114190693807813699 17597872671286040711720549)
                ·
                  refine ⟨3299601125866132633447603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17597872671286040711720549 3299601125866132633447603)
                  ·
                    refine ⟨4949401688799198950171405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299601125866132633447603 4949401688799198950171405)
                    ·
                      refine ⟨1856025633299699606314277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949401688799198950171405 1856025633299699606314277)
                      ·
                        rfl

theorem cell23_3614597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_3614597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614597 prefixEnd_3614597 := by exact prefixLift 3614597
  have htrace : WordTrace (prefixWord ++ tailWord_3614597) baseStart_3614597 baseEnd_3614597 := by
    simpa [prefixWord, tailWord_3614597, baseEnd_3614597] using wordTrace_append hprefix tailTrace_3614597
  have hstable : (prefixWord ++ tailWord_3614597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614597).length < 2 ^ (prefixWord ++ tailWord_3614597).sum := by decide
  have hdescent : baseEnd_3614597 < baseStart_3614597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614632 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3614632 : Nat := 118140960795 + 3614632 * 2 ^ 59
def prefixEnd_3614632 : Nat := 4983230072969 + 3 ^ 40 * 3614632 * 2
def baseEnd_3614632 : Nat := 1856043605122606969376617

theorem tailTrace_3614632 : CollatzResearch.WordTrace tailWord_3614632 prefixEnd_3614632 1856043605122606969376617 := by
  unfold tailWord_3614632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65918229920406534421279075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87890973227208712561705433 65918229920406534421279075)
  ·
    refine ⟨98877344880609801631918613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65918229920406534421279075 98877344880609801631918613)
    ·
      refine ⟨4634875541278584451496185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98877344880609801631918613 4634875541278584451496185)
      ·
        refine ⟨3476156655958938338622139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634875541278584451496185 3476156655958938338622139)
        ·
          refine ⟨5214234983938407507933209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476156655958938338622139 5214234983938407507933209)
          ·
            refine ⟨3910676237953805630949907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5214234983938407507933209 3910676237953805630949907)
            ·
              refine ⟨5866014356930708446424861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910676237953805630949907 5866014356930708446424861)
              ·
                refine ⟨2199755383849015667409323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5866014356930708446424861 2199755383849015667409323)
                ·
                  refine ⟨3299633075773523501113985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199755383849015667409323 3299633075773523501113985)
                  ·
                    refine ⟨2474724806830142625835489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3299633075773523501113985 2474724806830142625835489)
                    ·
                      refine ⟨1856043605122606969376617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474724806830142625835489 1856043605122606969376617)
                      ·
                        rfl

theorem cell23_3614632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3614632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614632 prefixEnd_3614632 := by exact prefixLift 3614632
  have htrace : WordTrace (prefixWord ++ tailWord_3614632) baseStart_3614632 baseEnd_3614632 := by
    simpa [prefixWord, tailWord_3614632, baseEnd_3614632] using wordTrace_append hprefix tailTrace_3614632
  have hstable : (prefixWord ++ tailWord_3614632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614632).length < 2 ^ (prefixWord ++ tailWord_3614632).sum := by decide
  have hdescent : baseEnd_3614632 < baseStart_3614632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614650 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_3614650 : Nat := 118140960795 + 3614650 * 2 ^ 59
def prefixEnd_3614650 : Nat := 4983230072969 + 3 ^ 40 * 3614650 * 2
def baseEnd_3614650 : Nat := 1856052847774387898951533

theorem tailTrace_3614650 : CollatzResearch.WordTrace tailWord_3614650 prefixEnd_3614650 1856052847774387898951533 := by
  unfold tailWord_3614650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32959279088686964479178351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87891410903165238611142269 32959279088686964479178351)
  ·
    refine ⟨49438918633030446718767527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32959279088686964479178351 49438918633030446718767527)
    ·
      refine ⟨74158377949545670078151291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49438918633030446718767527 74158377949545670078151291)
      ·
        refine ⟨111237566924318505117226937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74158377949545670078151291 111237566924318505117226937)
        ·
          refine ⟨83428175193238878837920203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111237566924318505117226937 83428175193238878837920203)
          ·
            refine ⟨125142262789858318256880305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83428175193238878837920203 125142262789858318256880305)
            ·
              refine ⟨93856697092393738692660229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125142262789858318256880305 93856697092393738692660229)
              ·
                refine ⟨17598130704823826004873793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93856697092393738692660229 17598130704823826004873793)
                ·
                  refine ⟨13198598028617869503655345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17598130704823826004873793 13198598028617869503655345)
                  ·
                    refine ⟨9898948521463402127741509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13198598028617869503655345 9898948521463402127741509)
                    ·
                      refine ⟨1856052847774387898951533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9898948521463402127741509 1856052847774387898951533)
                      ·
                        rfl

theorem cell23_3614650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_3614650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614650 prefixEnd_3614650 := by exact prefixLift 3614650
  have htrace : WordTrace (prefixWord ++ tailWord_3614650) baseStart_3614650 baseEnd_3614650 := by
    simpa [prefixWord, tailWord_3614650, baseEnd_3614650] using wordTrace_append hprefix tailTrace_3614650
  have hstable : (prefixWord ++ tailWord_3614650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614650).length < 2 ^ (prefixWord ++ tailWord_3614650).sum := by decide
  have hdescent : baseEnd_3614650 < baseStart_3614650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614741 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3614741 : Nat := 118140960795 + 3614741 * 2 ^ 59
def prefixEnd_3614741 : Nat := 4983230072969 + 3 ^ 40 * 3614741 * 2
def baseEnd_3614741 : Nat := 618699858171315680971205

theorem tailTrace_3614741 : CollatzResearch.WordTrace tailWord_3614741 prefixEnd_3614741 618699858171315680971205 := by
  unfold tailWord_3614741
  simp only [CollatzResearch.WordTrace]
  refine ⟨131840435397418180458276077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87893623598278786972184051 131840435397418180458276077)
  ·
    refine ⟨49440163274031817671853529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131840435397418180458276077 49440163274031817671853529)
    ·
      refine ⟨37080122455523863253890147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49440163274031817671853529 37080122455523863253890147)
      ·
        refine ⟨55620183683285794880835221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37080122455523863253890147 55620183683285794880835221)
        ·
          refine ⟨2607196110154021635039151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55620183683285794880835221 2607196110154021635039151)
          ·
            refine ⟨3910794165231032452558727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607196110154021635039151 3910794165231032452558727)
            ·
              refine ⟨5866191247846548678838091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910794165231032452558727 5866191247846548678838091)
              ·
                refine ⟨8799286871769823018257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866191247846548678838091 8799286871769823018257137)
                ·
                  refine ⟨6599465153827367263692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799286871769823018257137 6599465153827367263692853)
                  ·
                    refine ⟨618699858171315680971205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6599465153827367263692853 618699858171315680971205)
                    ·
                      rfl

theorem cell23_3614741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3614741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614741 prefixEnd_3614741 := by exact prefixLift 3614741
  have htrace : WordTrace (prefixWord ++ tailWord_3614741) baseStart_3614741 baseEnd_3614741 := by
    simpa [prefixWord, tailWord_3614741, baseEnd_3614741] using wordTrace_append hprefix tailTrace_3614741
  have hstable : (prefixWord ++ tailWord_3614741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614741).length < 2 ^ (prefixWord ++ tailWord_3614741).sum := by decide
  have hdescent : baseEnd_3614741 < baseStart_3614741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614747 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3]
def baseStart_3614747 : Nat := 118140960795 + 3614747 * 2 ^ 59
def prefixEnd_3614747 : Nat := 4983230072969 + 3 ^ 40 * 3614747 * 2
def baseEnd_3614747 : Nat := 1856102655397874019438587

theorem tailTrace_3614747 : CollatzResearch.WordTrace tailWord_3614747 prefixEnd_3614747 1856102655397874019438587 := by
  unfold tailWord_3614747
  simp only [CollatzResearch.WordTrace]
  refine ⟨131840654235396443482994495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87893769490264295655329663 131840654235396443482994495)
  ·
    refine ⟨197760981353094665224491743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131840654235396443482994495 197760981353094665224491743)
    ·
      refine ⟨296641472029641997836737615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197760981353094665224491743 296641472029641997836737615)
      ·
        refine ⟨444962208044462996755106423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296641472029641997836737615 444962208044462996755106423)
        ·
          refine ⟨667443312066694495132659635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444962208044462996755106423 667443312066694495132659635)
          ·
            refine ⟨1001164968100041742698989453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667443312066694495132659635 1001164968100041742698989453)
            ·
              refine ⟨375436863037515653512121045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001164968100041742698989453 375436863037515653512121045)
              ·
                refine ⟨8799301477441773129190337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 375436863037515653512121045 8799301477441773129190337)
                ·
                  refine ⟨6599476108081329846892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799301477441773129190337 6599476108081329846892753)
                  ·
                    refine ⟨4949607081060997385169565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599476108081329846892753 4949607081060997385169565)
                    ·
                      refine ⟨1856102655397874019438587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4949607081060997385169565 1856102655397874019438587)
                      ·
                        rfl

theorem cell23_3614747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].length) (baseStart_3614747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614747 prefixEnd_3614747 := by exact prefixLift 3614747
  have htrace : WordTrace (prefixWord ++ tailWord_3614747) baseStart_3614747 baseEnd_3614747 := by
    simpa [prefixWord, tailWord_3614747, baseEnd_3614747] using wordTrace_append hprefix tailTrace_3614747
  have hstable : (prefixWord ++ tailWord_3614747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614747).length < 2 ^ (prefixWord ++ tailWord_3614747).sum := by decide
  have hdescent : baseEnd_3614747 < baseStart_3614747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614784 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 6]
def baseStart_3614784 : Nat := 118140960795 + 3614784 * 2 ^ 59
def prefixEnd_3614784 : Nat := 4983230072969 + 3 ^ 40 * 3614784 * 2
def baseEnd_3614784 : Nat := 206235739353565597186213

theorem tailTrace_3614784 : CollatzResearch.WordTrace tailWord_3614784 prefixEnd_3614784 206235739353565597186213 := by
  unfold tailWord_3614784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65921001868131199401045703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87894669157508265868060937 65921001868131199401045703)
  ·
    refine ⟨98881502802196799101568555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65921001868131199401045703 98881502802196799101568555)
    ·
      refine ⟨148322254203295198652352833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98881502802196799101568555 148322254203295198652352833)
      ·
        refine ⟨111241690652471398989264625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148322254203295198652352833 111241690652471398989264625)
        ·
          refine ⟨83431267989353549241948469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111241690652471398989264625 83431267989353549241948469)
          ·
            refine ⟨7821681374001895241432669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83431267989353549241948469 7821681374001895241432669)
            ·
              refine ⟨2933130515250710715537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7821681374001895241432669 2933130515250710715537251)
              ·
                refine ⟨4399695772876066073305877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933130515250710715537251 4399695772876066073305877)
                ·
                  refine ⟨206235739353565597186213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4399695772876066073305877 206235739353565597186213)
                  ·
                    rfl

theorem cell23_3614784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_3614784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614784 prefixEnd_3614784 := by exact prefixLift 3614784
  have htrace : WordTrace (prefixWord ++ tailWord_3614784) baseStart_3614784 baseEnd_3614784 := by
    simpa [prefixWord, tailWord_3614784, baseEnd_3614784] using wordTrace_append hprefix tailTrace_3614784
  have hstable : (prefixWord ++ tailWord_3614784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614784).length < 2 ^ (prefixWord ++ tailWord_3614784).sum := by decide
  have hdescent : baseEnd_3614784 < baseStart_3614784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614817 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3614817 : Nat := 118140960795 + 3614817 * 2 ^ 59
def prefixEnd_3614817 : Nat := 4983230072969 + 3 ^ 40 * 3614817 * 2
def baseEnd_3614817 : Nat := 1856138599043688745563265

theorem tailTrace_3614817 : CollatzResearch.WordTrace tailWord_3614817 prefixEnd_3614817 1856138599043688745563265 := by
  unfold tailWord_3614817
  simp only [CollatzResearch.WordTrace]
  refine ⟨131843207345142845438042705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87895471563428563625361803 131843207345142845438042705)
  ·
    refine ⟨98882405508857134078532029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131843207345142845438042705 98882405508857134078532029)
    ·
      refine ⟨37080902065821425279449511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98882405508857134078532029 37080902065821425279449511)
      ·
        refine ⟨55621353098732137919174267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37080902065821425279449511 55621353098732137919174267)
        ·
          refine ⟨83432029648098206878761401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55621353098732137919174267 83432029648098206878761401)
          ·
            refine ⟨62574022236073655159071051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83432029648098206878761401 62574022236073655159071051)
            ·
              refine ⟨93861033354110482738606577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62574022236073655159071051 93861033354110482738606577)
              ·
                refine ⟨70395775015582862053954933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93861033354110482738606577 70395775015582862053954933)
                ·
                  refine ⟨6599603907710893317558275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70395775015582862053954933 6599603907710893317558275)
                  ·
                    refine ⟨9899405861566339976337413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6599603907710893317558275 9899405861566339976337413)
                    ·
                      refine ⟨1856138599043688745563265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9899405861566339976337413 1856138599043688745563265)
                      ·
                        rfl

theorem cell23_3614817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3614817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614817 prefixEnd_3614817 := by exact prefixLift 3614817
  have htrace : WordTrace (prefixWord ++ tailWord_3614817) baseStart_3614817 baseEnd_3614817 := by
    simpa [prefixWord, tailWord_3614817, baseEnd_3614817] using wordTrace_append hprefix tailTrace_3614817
  have hstable : (prefixWord ++ tailWord_3614817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614817).length < 2 ^ (prefixWord ++ tailWord_3614817).sum := by decide
  have hdescent : baseEnd_3614817 < baseStart_3614817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614821 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_3614821 : Nat := 118140960795 + 3614821 * 2 ^ 59
def prefixEnd_3614821 : Nat := 4983230072969 + 3 ^ 40 * 3614821 * 2
def baseEnd_3614821 : Nat := 1856140652966306729913247

theorem tailTrace_3614821 : CollatzResearch.WordTrace tailWord_3614821 prefixEnd_3614821 1856140652966306729913247 := by
  unfold tailWord_3614821
  simp only [CollatzResearch.WordTrace]
  refine ⟨131843353237128354121188317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87895568824752236080792211 131843353237128354121188317)
  ·
    refine ⟨49441257463923132795445619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131843353237128354121188317 49441257463923132795445619)
    ·
      refine ⟨74161886195884699193168429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49441257463923132795445619 74161886195884699193168429)
      ·
        refine ⟨27810707323456762197438161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74161886195884699193168429 27810707323456762197438161)
        ·
          refine ⟨20858030492592571648078621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27810707323456762197438161 20858030492592571648078621)
          ·
            refine ⟨7821761434722214368029483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20858030492592571648078621 7821761434722214368029483)
            ·
              refine ⟨11732642152083321552044225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821761434722214368029483 11732642152083321552044225)
              ·
                refine ⟨8799481614062491164033169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732642152083321552044225 8799481614062491164033169)
                ·
                  refine ⟨6599611210546868373024877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799481614062491164033169 6599611210546868373024877)
                  ·
                    refine ⟨2474854203955075639884329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6599611210546868373024877 2474854203955075639884329)
                    ·
                      refine ⟨1856140652966306729913247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474854203955075639884329 1856140652966306729913247)
                      ·
                        rfl

theorem cell23_3614821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_3614821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614821 prefixEnd_3614821 := by exact prefixLift 3614821
  have htrace : WordTrace (prefixWord ++ tailWord_3614821) baseStart_3614821 baseEnd_3614821 := by
    simpa [prefixWord, tailWord_3614821, baseEnd_3614821] using wordTrace_append hprefix tailTrace_3614821
  have hstable : (prefixWord ++ tailWord_3614821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614821).length < 2 ^ (prefixWord ++ tailWord_3614821).sum := by decide
  have hdescent : baseEnd_3614821 < baseStart_3614821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614851 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 4]
def baseStart_3614851 : Nat := 118140960795 + 3614851 * 2 ^ 59
def prefixEnd_3614851 : Nat := 4983230072969 + 3 ^ 40 * 3614851 * 2
def baseEnd_3614851 : Nat := 1856156057385941612538109

theorem tailTrace_3614851 : CollatzResearch.WordTrace tailWord_3614851 prefixEnd_3614851 1856156057385941612538109 := by
  unfold tailWord_3614851
  simp only [CollatzResearch.WordTrace]
  refine ⟨131844447427019669244780407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87896298284679779496520271 131844447427019669244780407)
  ·
    refine ⟨197766671140529503867170611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131844447427019669244780407 197766671140529503867170611)
    ·
      refine ⟨296650006710794255800755917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197766671140529503867170611 296650006710794255800755917)
      ·
        refine ⟨111243752516547845925283469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296650006710794255800755917 111243752516547845925283469)
        ·
          refine ⟨41716407193705442221981301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111243752516547845925283469 41716407193705442221981301)
          ·
            refine ⟨3910913174409885208310747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41716407193705442221981301 3910913174409885208310747)
            ·
              refine ⟨5866369761614827812466121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910913174409885208310747 5866369761614827812466121)
              ·
                refine ⟨4399777321211120859349591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5866369761614827812466121 4399777321211120859349591)
                ·
                  refine ⟨6599665981816681289024387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399777321211120859349591 6599665981816681289024387)
                  ·
                    refine ⟨9899498972725021933536581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6599665981816681289024387 9899498972725021933536581)
                    ·
                      refine ⟨1856156057385941612538109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9899498972725021933536581 1856156057385941612538109)
                      ·
                        rfl

theorem cell23_3614851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_3614851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614851 prefixEnd_3614851 := by exact prefixLift 3614851
  have htrace : WordTrace (prefixWord ++ tailWord_3614851) baseStart_3614851 baseEnd_3614851 := by
    simpa [prefixWord, tailWord_3614851, baseEnd_3614851] using wordTrace_append hprefix tailTrace_3614851
  have hstable : (prefixWord ++ tailWord_3614851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614851).length < 2 ^ (prefixWord ++ tailWord_3614851).sum := by decide
  have hdescent : baseEnd_3614851 < baseStart_3614851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614871 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3614871 : Nat := 118140960795 + 3614871 * 2 ^ 59
def prefixEnd_3614871 : Nat := 4983230072969 + 3 ^ 40 * 3614871 * 2
def baseEnd_3614871 : Nat := 1856166326999031534288017

theorem tailTrace_3614871 : CollatzResearch.WordTrace tailWord_3614871 prefixEnd_3614871 1856166326999031534288017 := by
  unfold tailWord_3614871
  simp only [CollatzResearch.WordTrace]
  refine ⟨131845176886947212660508467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87896784591298141773672311 131845176886947212660508467)
  ·
    refine ⟨197767765330420818990762701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131845176886947212660508467 197767765330420818990762701)
    ·
      refine ⟨74162911998907807121536013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197767765330420818990762701 74162911998907807121536013)
      ·
        refine ⟨27811091999590427670576005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74162911998907807121536013 27811091999590427670576005)
        ·
          refine ⟨5214579749923205188233001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27811091999590427670576005 5214579749923205188233001)
          ·
            refine ⟨3910934812442403891174751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5214579749923205188233001 3910934812442403891174751)
            ·
              refine ⟨5866402218663605836762127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910934812442403891174751 5866402218663605836762127)
              ·
                refine ⟨8799603327995408755143191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866402218663605836762127 8799603327995408755143191)
                ·
                  refine ⟨13199404991993113132714787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8799603327995408755143191 13199404991993113132714787)
                  ·
                    refine ⟨19799107487989669699072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13199404991993113132714787 19799107487989669699072181)
                    ·
                      refine ⟨1856166326999031534288017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19799107487989669699072181 1856166326999031534288017)
                      ·
                        rfl

theorem cell23_3614871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3614871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614871 prefixEnd_3614871 := by exact prefixLift 3614871
  have htrace : WordTrace (prefixWord ++ tailWord_3614871) baseStart_3614871 baseEnd_3614871 := by
    simpa [prefixWord, tailWord_3614871, baseEnd_3614871] using wordTrace_append hprefix tailTrace_3614871
  have hstable : (prefixWord ++ tailWord_3614871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614871).length < 2 ^ (prefixWord ++ tailWord_3614871).sum := by decide
  have hdescent : baseEnd_3614871 < baseStart_3614871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614874 : List Nat := [3, 1, 1, 5, 3, 10]
def baseStart_3614874 : Nat := 118140960795 + 3614874 * 2 ^ 59
def prefixEnd_3614874 : Nat := 4983230072969 + 3 ^ 40 * 3614874 * 2
def baseEnd_3614874 : Nat := 7638550894818909557821

theorem tailTrace_3614874 : CollatzResearch.WordTrace tailWord_3614874 prefixEnd_3614874 7638550894818909557821 := by
  unfold tailWord_3614874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32961321576484086043216919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87896857537290896115245117 32961321576484086043216919)
  ·
    refine ⟨49441982364726129064825379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32961321576484086043216919 49441982364726129064825379)
    ·
      refine ⟨74162973547089193597238069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49441982364726129064825379 74162973547089193597238069)
      ·
        refine ⟨6952778770039611899741069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74162973547089193597238069 6952778770039611899741069)
        ·
          refine ⟨2607292038764854462402901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6952778770039611899741069 2607292038764854462402901)
          ·
            refine ⟨7638550894818909557821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2607292038764854462402901 7638550894818909557821)
            ·
              rfl

theorem cell23_3614874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 10].length) (baseStart_3614874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614874 prefixEnd_3614874 := by exact prefixLift 3614874
  have htrace : WordTrace (prefixWord ++ tailWord_3614874) baseStart_3614874 baseEnd_3614874 := by
    simpa [prefixWord, tailWord_3614874, baseEnd_3614874] using wordTrace_append hprefix tailTrace_3614874
  have hstable : (prefixWord ++ tailWord_3614874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614874).length < 2 ^ (prefixWord ++ tailWord_3614874).sum := by decide
  have hdescent : baseEnd_3614874 < baseStart_3614874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614907 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_3614907 : Nat := 118140960795 + 3614907 * 2 ^ 59
def prefixEnd_3614907 : Nat := 4983230072969 + 3 ^ 40 * 3614907 * 2
def baseEnd_3614907 : Nat := 1856184812302593393437851

theorem tailTrace_3614907 : CollatzResearch.WordTrace tailWord_3614907 prefixEnd_3614907 1856184812302593393437851 := by
  unfold tailWord_3614907
  simp only [CollatzResearch.WordTrace]
  refine ⟨131846489914816790808818975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87897659943211193872545983 131846489914816790808818975)
  ·
    refine ⟨197769734872225186213228463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131846489914816790808818975 197769734872225186213228463)
    ·
      refine ⟨296654602308337779319842695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197769734872225186213228463 296654602308337779319842695)
      ·
        refine ⟨444981903462506668979764043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296654602308337779319842695 444981903462506668979764043)
        ·
          refine ⟨667472855193760003469646065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444981903462506668979764043 667472855193760003469646065)
          ·
            refine ⟨500604641395320002602234549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667472855193760003469646065 500604641395320002602234549)
            ·
              refine ⟨46931685130811250243959489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 500604641395320002602234549 46931685130811250243959489)
              ·
                refine ⟨35198763848108437682969617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46931685130811250243959489 35198763848108437682969617)
                ·
                  refine ⟨26399072886081328262227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35198763848108437682969617 26399072886081328262227213)
                  ·
                    refine ⟨9899652332280498098335205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26399072886081328262227213 9899652332280498098335205)
                    ·
                      refine ⟨1856184812302593393437851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9899652332280498098335205 1856184812302593393437851)
                      ·
                        rfl

theorem cell23_3614907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_3614907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614907 prefixEnd_3614907 := by exact prefixLift 3614907
  have htrace : WordTrace (prefixWord ++ tailWord_3614907) baseStart_3614907 baseEnd_3614907 := by
    simpa [prefixWord, tailWord_3614907, baseEnd_3614907] using wordTrace_append hprefix tailTrace_3614907
  have hstable : (prefixWord ++ tailWord_3614907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614907).length < 2 ^ (prefixWord ++ tailWord_3614907).sum := by decide
  have hdescent : baseEnd_3614907 < baseStart_3614907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614911 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 1, 3, 2]
def baseStart_3614911 : Nat := 118140960795 + 3614911 * 2 ^ 59
def prefixEnd_3614911 : Nat := 4983230072969 + 3 ^ 40 * 3614911 * 2
def baseEnd_3614911 : Nat := 1856186866225211377787833

theorem tailTrace_3614911 : CollatzResearch.WordTrace tailWord_3614911 prefixEnd_3614911 1856186866225211377787833 := by
  unfold tailWord_3614911
  simp only [CollatzResearch.WordTrace]
  refine ⟨131846635806802299491964587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87897757204534866327976391 131846635806802299491964587)
  ·
    refine ⟨197769953710203449237946881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131846635806802299491964587 197769953710203449237946881)
    ·
      refine ⟨148327465282652586928460161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197769953710203449237946881 148327465282652586928460161)
      ·
        refine ⟨111245598961989440196345121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148327465282652586928460161 111245598961989440196345121)
        ·
          refine ⟨83434199221492080147258841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111245598961989440196345121 83434199221492080147258841)
          ·
            refine ⟨62575649416119060110444131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83434199221492080147258841 62575649416119060110444131)
            ·
              refine ⟨93863474124178590165666197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62575649416119060110444131 93863474124178590165666197)
              ·
                refine ⟨4399850349570871414015603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93863474124178590165666197 4399850349570871414015603)
                ·
                  refine ⟨6599775524356307121023405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399850349570871414015603 6599775524356307121023405)
                  ·
                    refine ⟨2474915821633615170383777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6599775524356307121023405 2474915821633615170383777)
                    ·
                      refine ⟨1856186866225211377787833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2474915821633615170383777 1856186866225211377787833)
                      ·
                        rfl

theorem cell23_3614911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_3614911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614911 prefixEnd_3614911 := by exact prefixLift 3614911
  have htrace : WordTrace (prefixWord ++ tailWord_3614911) baseStart_3614911 baseEnd_3614911 := by
    simpa [prefixWord, tailWord_3614911, baseEnd_3614911] using wordTrace_append hprefix tailTrace_3614911
  have hstable : (prefixWord ++ tailWord_3614911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614911).length < 2 ^ (prefixWord ++ tailWord_3614911).sum := by decide
  have hdescent : baseEnd_3614911 < baseStart_3614911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614927 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_3614927 : Nat := 118140960795 + 3614927 * 2 ^ 59
def prefixEnd_3614927 : Nat := 4983230072969 + 3 ^ 40 * 3614927 * 2
def baseEnd_3614927 : Nat := 1856195081915683315187759

theorem tailTrace_3614927 : CollatzResearch.WordTrace tailWord_3614927 prefixEnd_3614927 1856195081915683315187759 := by
  unfold tailWord_3614927
  simp only [CollatzResearch.WordTrace]
  refine ⟨131847219374744334224547035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87898146249829556149698023 131847219374744334224547035)
  ·
    refine ⟨197770829062116501336820553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131847219374744334224547035 197770829062116501336820553)
    ·
      refine ⟨148328121796587376002615415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197770829062116501336820553 148328121796587376002615415)
      ·
        refine ⟨222492182694881064003923123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148328121796587376002615415 222492182694881064003923123)
        ·
          refine ⟨333738274042321596005884685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222492182694881064003923123 333738274042321596005884685)
          ·
            refine ⟨125151852765870598502206757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333738274042321596005884685 125151852765870598502206757)
            ·
              refine ⟨23465972393600737219163767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125151852765870598502206757 23465972393600737219163767)
              ·
                refine ⟨35198958590401105828745651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23465972393600737219163767 35198958590401105828745651)
                ·
                  refine ⟨52798437885601658743118477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35198958590401105828745651 52798437885601658743118477)
                  ·
                    refine ⟨19799414207100622028669429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52798437885601658743118477 19799414207100622028669429)
                    ·
                      refine ⟨1856195081915683315187759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19799414207100622028669429 1856195081915683315187759)
                      ·
                        rfl

theorem cell23_3614927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_3614927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614927 prefixEnd_3614927 := by exact prefixLift 3614927
  have htrace : WordTrace (prefixWord ++ tailWord_3614927) baseStart_3614927 baseEnd_3614927 := by
    simpa [prefixWord, tailWord_3614927, baseEnd_3614927] using wordTrace_append hprefix tailTrace_3614927
  have hstable : (prefixWord ++ tailWord_3614927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614927).length < 2 ^ (prefixWord ++ tailWord_3614927).sum := by decide
  have hdescent : baseEnd_3614927 < baseStart_3614927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3614954 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3614954 : Nat := 118140960795 + 3614954 * 2 ^ 59
def prefixEnd_3614954 : Nat := 4983230072969 + 3 ^ 40 * 3614954 * 2
def baseEnd_3614954 : Nat := 1856208945893354709550135

theorem tailTrace_3614954 : CollatzResearch.WordTrace tailWord_3614954 prefixEnd_3614954 1856208945893354709550135 := by
  unfold tailWord_3614954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32962051036411629458944979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87898802763764345223853277 32962051036411629458944979)
  ·
    refine ⟨49443076554617444188417469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32962051036411629458944979 49443076554617444188417469)
    ·
      refine ⟨18541153707981541570656551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49443076554617444188417469 18541153707981541570656551)
      ·
        refine ⟨27811730561972312355984827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18541153707981541570656551 27811730561972312355984827)
        ·
          refine ⟨41717595842958468533977241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27811730561972312355984827 41717595842958468533977241)
          ·
            refine ⟨31288196882218851400482931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41717595842958468533977241 31288196882218851400482931)
            ·
              refine ⟨46932295323328277100724397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31288196882218851400482931 46932295323328277100724397)
              ·
                refine ⟨17599610746248103912771649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46932295323328277100724397 17599610746248103912771649)
                ·
                  refine ⟨13199708059686077934578737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17599610746248103912771649 13199708059686077934578737)
                  ·
                    refine ⟨9899781044764558450934053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13199708059686077934578737 9899781044764558450934053)
                    ·
                      refine ⟨1856208945893354709550135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9899781044764558450934053 1856208945893354709550135)
                      ·
                        rfl

theorem cell23_3614954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3614954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3614954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3614954 prefixEnd_3614954 := by exact prefixLift 3614954
  have htrace : WordTrace (prefixWord ++ tailWord_3614954) baseStart_3614954 baseEnd_3614954 := by
    simpa [prefixWord, tailWord_3614954, baseEnd_3614954] using wordTrace_append hprefix tailTrace_3614954
  have hstable : (prefixWord ++ tailWord_3614954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3614954).length < 2 ^ (prefixWord ++ tailWord_3614954).sum := by decide
  have hdescent : baseEnd_3614954 < baseStart_3614954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3614954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615028 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3615028 : Nat := 118140960795 + 3615028 * 2 ^ 59
def prefixEnd_3615028 : Nat := 4983230072969 + 3 ^ 40 * 3615028 * 2
def baseEnd_3615028 : Nat := 618748981153929140008265

theorem tailTrace_3615028 : CollatzResearch.WordTrace tailWord_3615028 prefixEnd_3615028 618748981153929140008265 := by
  unfold tailWord_3615028
  simp only [CollatzResearch.WordTrace]
  refine ⟨65925451573689214236986869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87900602098252285649315825 65925451573689214236986869)
  ·
    refine ⟨6180511085033363834717519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65925451573689214236986869 6180511085033363834717519)
    ·
      refine ⟨9270766627550045752076279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180511085033363834717519 9270766627550045752076279)
      ·
        refine ⟨13906149941325068628114419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270766627550045752076279 13906149941325068628114419)
        ·
          refine ⟨20859224911987602942171629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906149941325068628114419 20859224911987602942171629)
          ·
            refine ⟨7822209341995351103314361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20859224911987602942171629 7822209341995351103314361)
            ·
              refine ⟨5866657006496513327485771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7822209341995351103314361 5866657006496513327485771)
              ·
                refine ⟨8799985509744769991228657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866657006496513327485771 8799985509744769991228657)
                ·
                  refine ⟨6599989132308577493421493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8799985509744769991228657 6599989132308577493421493)
                  ·
                    refine ⟨618748981153929140008265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6599989132308577493421493 618748981153929140008265)
                    ·
                      rfl

theorem cell23_3615028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3615028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615028 prefixEnd_3615028 := by exact prefixLift 3615028
  have htrace : WordTrace (prefixWord ++ tailWord_3615028) baseStart_3615028 baseEnd_3615028 := by
    simpa [prefixWord, tailWord_3615028, baseEnd_3615028] using wordTrace_append hprefix tailTrace_3615028
  have hstable : (prefixWord ++ tailWord_3615028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615028).length < 2 ^ (prefixWord ++ tailWord_3615028).sum := by decide
  have hdescent : baseEnd_3615028 < baseStart_3615028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615091 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 5, 2]
def baseStart_3615091 : Nat := 118140960795 + 3615091 * 2 ^ 59
def prefixEnd_3615091 : Nat := 4983230072969 + 3 ^ 40 * 3615091 * 2
def baseEnd_3615091 : Nat := 1856279292743020673537005

theorem tailTrace_3615091 : CollatzResearch.WordTrace tailWord_3615091 prefixEnd_3615091 1856279292743020673537005 := by
  unfold tailWord_3615091
  simp only [CollatzResearch.WordTrace]
  refine ⟨131853200946150190233517127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87902133964100126822344751 131853200946150190233517127)
  ·
    refine ⟨197779801419225285350275691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131853200946150190233517127 197779801419225285350275691)
    ·
      refine ⟨296669702128837928025413537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197779801419225285350275691 296669702128837928025413537)
      ·
        refine ⟨222502276596628446019060153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296669702128837928025413537 222502276596628446019060153)
        ·
          refine ⟨166876707447471334514295115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222502276596628446019060153 166876707447471334514295115)
          ·
            refine ⟨250315061171207001771442673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166876707447471334514295115 250315061171207001771442673)
            ·
              refine ⟨187736295878405251328582005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250315061171207001771442673 187736295878405251328582005)
              ·
                refine ⟨17600277738600492312054563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187736295878405251328582005 17600277738600492312054563)
                ·
                  refine ⟨26400416607900738468081845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17600277738600492312054563 26400416607900738468081845)
                  ·
                    refine ⟨2475039056990694231382673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26400416607900738468081845 2475039056990694231382673)
                    ·
                      refine ⟨1856279292743020673537005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475039056990694231382673 1856279292743020673537005)
                      ·
                        rfl

theorem cell23_3615091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5, 2].length) (baseStart_3615091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615091 prefixEnd_3615091 := by exact prefixLift 3615091
  have htrace : WordTrace (prefixWord ++ tailWord_3615091) baseStart_3615091 baseEnd_3615091 := by
    simpa [prefixWord, tailWord_3615091, baseEnd_3615091] using wordTrace_append hprefix tailTrace_3615091
  have hstable : (prefixWord ++ tailWord_3615091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615091).length < 2 ^ (prefixWord ++ tailWord_3615091).sum := by decide
  have hdescent : baseEnd_3615091 < baseStart_3615091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615108 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3615108 : Nat := 118140960795 + 3615108 * 2 ^ 59
def prefixEnd_3615108 : Nat := 4983230072969 + 3 ^ 40 * 3615108 * 2
def baseEnd_3615108 : Nat := 1856288021914147107024427

theorem tailTrace_3615108 : CollatzResearch.WordTrace tailWord_3615108 prefixEnd_3615108 1856288021914147107024427 := by
  unfold tailWord_3615108
  simp only [CollatzResearch.WordTrace]
  refine ⟨65926910493544301068442989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87902547324725734757923985 65926910493544301068442989)
  ·
    refine ⟨24722591435079112900666121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65926910493544301068442989 24722591435079112900666121)
    ·
      refine ⟨18541943576309334675499591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24722591435079112900666121 18541943576309334675499591)
      ·
        refine ⟨27812915364464002013249387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18541943576309334675499591 27812915364464002013249387)
        ·
          refine ⟨41719373046696003019874081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27812915364464002013249387 41719373046696003019874081)
          ·
            refine ⟨31289529785022002264905561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41719373046696003019874081 31289529785022002264905561)
            ·
              refine ⟨23467147338766501698679171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31289529785022002264905561 23467147338766501698679171)
              ·
                refine ⟨35200721008149752548018757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23467147338766501698679171 35200721008149752548018757)
                ·
                  refine ⟨6600135189028078602753517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35200721008149752548018757 6600135189028078602753517)
                  ·
                    refine ⟨2475050695885529476032569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6600135189028078602753517 2475050695885529476032569)
                    ·
                      refine ⟨1856288021914147107024427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475050695885529476032569 1856288021914147107024427)
                      ·
                        rfl

theorem cell23_3615108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3615108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615108 prefixEnd_3615108 := by exact prefixLift 3615108
  have htrace : WordTrace (prefixWord ++ tailWord_3615108) baseStart_3615108 baseEnd_3615108 := by
    simpa [prefixWord, tailWord_3615108, baseEnd_3615108] using wordTrace_append hprefix tailTrace_3615108
  have hstable : (prefixWord ++ tailWord_3615108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615108).length < 2 ^ (prefixWord ++ tailWord_3615108).sum := by decide
  have hdescent : baseEnd_3615108 < baseStart_3615108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615115 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 1, 1, 3]
def baseStart_3615115 : Nat := 118140960795 + 3615115 * 2 ^ 59
def prefixEnd_3615115 : Nat := 4983230072969 + 3 ^ 40 * 3615115 * 2
def baseEnd_3615115 : Nat := 1856291616278728579636895

theorem tailTrace_3615115 : CollatzResearch.WordTrace tailWord_3615115 prefixEnd_3615115 1856291616278728579636895 := by
  unfold tailWord_3615115
  simp only [CollatzResearch.WordTrace]
  refine ⟨131854076298063242332390799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87902717532042161554927199 131854076298063242332390799)
  ·
    refine ⟨197781114447094863498586199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131854076298063242332390799 197781114447094863498586199)
    ·
      refine ⟨296671671670642295247879299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197781114447094863498586199 296671671670642295247879299)
      ·
        refine ⟨445007507505963442871818949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296671671670642295247879299 445007507505963442871818949)
        ·
          refine ⟨83438907657368145538466053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445007507505963442871818949 83438907657368145538466053)
          ·
            refine ⟨15644795185756527288462385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83438907657368145538466053 15644795185756527288462385)
            ·
              refine ⟨11733596389317395466346789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15644795185756527288462385 11733596389317395466346789)
              ·
                refine ⟨2200049322997011649940023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11733596389317395466346789 2200049322997011649940023)
                ·
                  refine ⟨3300073984495517474910035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200049322997011649940023 3300073984495517474910035)
                  ·
                    refine ⟨4950110976743276212365053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300073984495517474910035 4950110976743276212365053)
                    ·
                      refine ⟨1856291616278728579636895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950110976743276212365053 1856291616278728579636895)
                      ·
                        rfl

theorem cell23_3615115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 1, 3].length) (baseStart_3615115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615115 prefixEnd_3615115 := by exact prefixLift 3615115
  have htrace : WordTrace (prefixWord ++ tailWord_3615115) baseStart_3615115 baseEnd_3615115 := by
    simpa [prefixWord, tailWord_3615115, baseEnd_3615115] using wordTrace_append hprefix tailTrace_3615115
  have hstable : (prefixWord ++ tailWord_3615115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615115).length < 2 ^ (prefixWord ++ tailWord_3615115).sum := by decide
  have hdescent : baseEnd_3615115 < baseStart_3615115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615121 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_3615121 : Nat := 118140960795 + 3615121 * 2 ^ 59
def prefixEnd_3615121 : Nat := 4983230072969 + 3 ^ 40 * 3615121 * 2
def baseEnd_3615121 : Nat := 1856294697162655556161867

theorem tailTrace_3615121 : CollatzResearch.WordTrace tailWord_3615121 prefixEnd_3615121 1856294697162655556161867 := by
  unfold tailWord_3615121
  simp only [CollatzResearch.WordTrace]
  refine ⟨131854295136041505357109217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87902863424027670238072811 131854295136041505357109217)
  ·
    refine ⟨98890721352031129017831913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131854295136041505357109217 98890721352031129017831913)
    ·
      refine ⟨74168041014023346763373935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98890721352031129017831913 74168041014023346763373935)
      ·
        refine ⟨111252061521035020145060903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74168041014023346763373935 111252061521035020145060903)
        ·
          refine ⟨166878092281552530217591355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111252061521035020145060903 166878092281552530217591355)
          ·
            refine ⟨250317138422328795326387033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166878092281552530217591355 250317138422328795326387033)
            ·
              refine ⟨187737853816746596494790275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250317138422328795326387033 187737853816746596494790275)
              ·
                refine ⟨281606780725119894742185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187737853816746596494790275 281606780725119894742185413)
                ·
                  refine ⟨52801271385959980264159765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281606780725119894742185413 52801271385959980264159765)
                  ·
                    refine ⟨2475059596216874074882489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52801271385959980264159765 2475059596216874074882489)
                    ·
                      refine ⟨1856294697162655556161867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475059596216874074882489 1856294697162655556161867)
                      ·
                        rfl

theorem cell23_3615121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_3615121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615121 prefixEnd_3615121 := by exact prefixLift 3615121
  have htrace : WordTrace (prefixWord ++ tailWord_3615121) baseStart_3615121 baseEnd_3615121 := by
    simpa [prefixWord, tailWord_3615121, baseEnd_3615121] using wordTrace_append hprefix tailTrace_3615121
  have hstable : (prefixWord ++ tailWord_3615121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615121).length < 2 ^ (prefixWord ++ tailWord_3615121).sum := by decide
  have hdescent : baseEnd_3615121 < baseStart_3615121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615138 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3615138 : Nat := 118140960795 + 3615138 * 2 ^ 59
def prefixEnd_3615138 : Nat := 4983230072969 + 3 ^ 40 * 3615138 * 2
def baseEnd_3615138 : Nat := 1856303426333781989649289

theorem tailTrace_3615138 : CollatzResearch.WordTrace tailWord_3615138 prefixEnd_3615138 1856303426333781989649289 := by
  unfold tailWord_3615138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32963728794244979315119517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87903276784653278173652045 32963728794244979315119517)
  ·
    refine ⟨12361398297841867243169819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32963728794244979315119517 12361398297841867243169819)
    ·
      refine ⟨18542097446762800864754729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361398297841867243169819 18542097446762800864754729)
      ·
        refine ⟨13906573085072100648566047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18542097446762800864754729 13906573085072100648566047)
        ·
          refine ⟨20859859627608150972849071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906573085072100648566047 20859859627608150972849071)
          ·
            refine ⟨31289789441412226459273607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20859859627608150972849071 31289789441412226459273607)
            ·
              refine ⟨46934684162118339688910411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31289789441412226459273607 46934684162118339688910411)
              ·
                refine ⟨70402026243177509533365617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46934684162118339688910411 70402026243177509533365617)
                ·
                  refine ⟨52801519682383132150024213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70402026243177509533365617 52801519682383132150024213)
                  ·
                    refine ⟨2475071235111709319532385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52801519682383132150024213 2475071235111709319532385)
                    ·
                      refine ⟨1856303426333781989649289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475071235111709319532385 1856303426333781989649289)
                      ·
                        rfl

theorem cell23_3615138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3615138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615138 prefixEnd_3615138 := by exact prefixLift 3615138
  have htrace : WordTrace (prefixWord ++ tailWord_3615138) baseStart_3615138 baseEnd_3615138 := by
    simpa [prefixWord, tailWord_3615138, baseEnd_3615138] using wordTrace_append hprefix tailTrace_3615138
  have hstable : (prefixWord ++ tailWord_3615138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615138).length < 2 ^ (prefixWord ++ tailWord_3615138).sum := by decide
  have hdescent : baseEnd_3615138 < baseStart_3615138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615161 : List Nat := [1, 2, 1, 4, 3, 3, 9]
def baseStart_3615161 : Nat := 118140960795 + 3615161 * 2 ^ 59
def prefixEnd_3615161 : Nat := 4983230072969 + 3 ^ 40 * 3615161 * 2
def baseEnd_3615161 : Nat := 22917472054183153082243

theorem tailTrace_3615161 : CollatzResearch.WordTrace tailWord_3615161 prefixEnd_3615161 22917472054183153082243 := by
  unfold tailWord_3615161
  simp only [CollatzResearch.WordTrace]
  refine ⟨131855754055896592188565337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87903836037264394792376891 131855754055896592188565337)
  ·
    refine ⟨98891815541922444141424003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131855754055896592188565337 98891815541922444141424003)
    ·
      refine ⟨148337723312883666212136005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98891815541922444141424003 148337723312883666212136005)
      ·
        refine ⟨27813323121165687414775501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148337723312883666212136005 27813323121165687414775501)
        ·
          refine ⟨10429996170437132780540813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27813323121165687414775501 10429996170437132780540813)
          ·
            refine ⟨3911248563913924792702805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10429996170437132780540813 3911248563913924792702805)
            ·
              refine ⟨22917472054183153082243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3911248563913924792702805 22917472054183153082243)
              ·
                rfl

theorem cell23_3615161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 9].length) (baseStart_3615161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615161 prefixEnd_3615161 := by exact prefixLift 3615161
  have htrace : WordTrace (prefixWord ++ tailWord_3615161) baseStart_3615161 baseEnd_3615161 := by
    simpa [prefixWord, tailWord_3615161, baseEnd_3615161] using wordTrace_append hprefix tailTrace_3615161
  have hstable : (prefixWord ++ tailWord_3615161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615161).length < 2 ^ (prefixWord ++ tailWord_3615161).sum := by decide
  have hdescent : baseEnd_3615161 < baseStart_3615161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615202 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3615202 : Nat := 118140960795 + 3615202 * 2 ^ 59
def prefixEnd_3615202 : Nat := 4983230072969 + 3 ^ 40 * 3615202 * 2
def baseEnd_3615202 : Nat := 1856336289095669739248995

theorem tailTrace_3615202 : CollatzResearch.WordTrace tailWord_3615202 prefixEnd_3615202 1856336289095669739248995 := by
  unfold tailWord_3615202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32964312362187014047701965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87904832965832037460538573 32964312362187014047701965)
  ·
    refine ⟨12361617135820130267888237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32964312362187014047701965 12361617135820130267888237)
    ·
      refine ⟨4635606425932548850458089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12361617135820130267888237 4635606425932548850458089)
      ·
        refine ⟨3476704819449411637843567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635606425932548850458089 3476704819449411637843567)
        ·
          refine ⟨5215057229174117456765351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476704819449411637843567 5215057229174117456765351)
          ·
            refine ⟨7822585843761176185148027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215057229174117456765351 7822585843761176185148027)
            ·
              refine ⟨11733878765641764277722041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822585843761176185148027 11733878765641764277722041)
              ·
                refine ⟨8800409074231323208291531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733878765641764277722041 8800409074231323208291531)
                ·
                  refine ⟨13200613611346984812437297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800409074231323208291531 13200613611346984812437297)
                  ·
                    refine ⟨9900460208510238609327973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13200613611346984812437297 9900460208510238609327973)
                    ·
                      refine ⟨1856336289095669739248995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9900460208510238609327973 1856336289095669739248995)
                      ·
                        rfl

theorem cell23_3615202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3615202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615202 prefixEnd_3615202 := by exact prefixLift 3615202
  have htrace : WordTrace (prefixWord ++ tailWord_3615202) baseStart_3615202 baseEnd_3615202 := by
    simpa [prefixWord, tailWord_3615202, baseEnd_3615202] using wordTrace_append hprefix tailTrace_3615202
  have hstable : (prefixWord ++ tailWord_3615202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615202).length < 2 ^ (prefixWord ++ tailWord_3615202).sum := by decide
  have hdescent : baseEnd_3615202 < baseStart_3615202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615205 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3615205 : Nat := 118140960795 + 3615205 * 2 ^ 59
def prefixEnd_3615205 : Nat := 4983230072969 + 3 ^ 40 * 3615205 * 2
def baseEnd_3615205 : Nat := 1856337829537633227511481

theorem tailTrace_3615205 : CollatzResearch.WordTrace tailWord_3615205 prefixEnd_3615205 1856337829537633227511481 := by
  unfold tailWord_3615205
  simp only [CollatzResearch.WordTrace]
  refine ⟨131857358867737187703167069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87904905911824791802111379 131857358867737187703167069)
  ·
    refine ⟨49446509575401445388687651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131857358867737187703167069 49446509575401445388687651)
    ·
      refine ⟨74169764363102168083031477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49446509575401445388687651 74169764363102168083031477)
      ·
        refine ⟨6953415409040828257784201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74169764363102168083031477 6953415409040828257784201)
        ·
          refine ⟨5215061556780621193338151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6953415409040828257784201 5215061556780621193338151)
          ·
            refine ⟨7822592335170931790007227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215061556780621193338151 7822592335170931790007227)
            ·
              refine ⟨11733888502756397685010841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822592335170931790007227 11733888502756397685010841)
              ·
                refine ⟨8800416377067298263758131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733888502756397685010841 8800416377067298263758131)
                ·
                  refine ⟨13200624565600947395637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800416377067298263758131 13200624565600947395637197)
                  ·
                    refine ⟨4950234212100355273363949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13200624565600947395637197 4950234212100355273363949)
                    ·
                      refine ⟨1856337829537633227511481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950234212100355273363949 1856337829537633227511481)
                      ·
                        rfl

theorem cell23_3615205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3615205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615205 prefixEnd_3615205 := by exact prefixLift 3615205
  have htrace : WordTrace (prefixWord ++ tailWord_3615205) baseStart_3615205 baseEnd_3615205 := by
    simpa [prefixWord, tailWord_3615205, baseEnd_3615205] using wordTrace_append hprefix tailTrace_3615205
  have hstable : (prefixWord ++ tailWord_3615205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615205).length < 2 ^ (prefixWord ++ tailWord_3615205).sum := by decide
  have hdescent : baseEnd_3615205 < baseStart_3615205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615222 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3615222 : Nat := 118140960795 + 3615222 * 2 ^ 59
def prefixEnd_3615222 : Nat := 4983230072969 + 3 ^ 40 * 3615222 * 2
def baseEnd_3615222 : Nat := 1856346558708759660998903

theorem tailTrace_3615222 : CollatzResearch.WordTrace tailWord_3615222 prefixEnd_3615222 1856346558708759660998903 := by
  unfold tailWord_3615222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241123681792224975408495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87905319272450399737690613 8241123681792224975408495)
  ·
    refine ⟨12361685522688337463112743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241123681792224975408495 12361685522688337463112743)
    ·
      refine ⟨18542528284032506194669115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361685522688337463112743 18542528284032506194669115)
      ·
        refine ⟨27813792426048759292003673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18542528284032506194669115 27813792426048759292003673)
        ·
          refine ⟨20860344319536569469002755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27813792426048759292003673 20860344319536569469002755)
          ·
            refine ⟨31290516479304854203504133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20860344319536569469002755 31290516479304854203504133)
            ·
              refine ⟨5866971839869660163157025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31290516479304854203504133 5866971839869660163157025)
              ·
                refine ⟨4400228879902245122367769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5866971839869660163157025 4400228879902245122367769)
                ·
                  refine ⟨3300171659926683841775827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400228879902245122367769 3300171659926683841775827)
                  ·
                    refine ⟨4950257489890025762663741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300171659926683841775827 4950257489890025762663741)
                    ·
                      refine ⟨1856346558708759660998903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950257489890025762663741 1856346558708759660998903)
                      ·
                        rfl

theorem cell23_3615222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3615222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615222 prefixEnd_3615222 := by exact prefixLift 3615222
  have htrace : WordTrace (prefixWord ++ tailWord_3615222) baseStart_3615222 baseEnd_3615222 := by
    simpa [prefixWord, tailWord_3615222, baseEnd_3615222] using wordTrace_append hprefix tailTrace_3615222
  have hstable : (prefixWord ++ tailWord_3615222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615222).length < 2 ^ (prefixWord ++ tailWord_3615222).sum := by decide
  have hdescent : baseEnd_3615222 < baseStart_3615222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_3615228 : Nat := 118140960795 + 3615228 * 2 ^ 59
def prefixEnd_3615228 : Nat := 4983230072969 + 3 ^ 40 * 3615228 * 2
def baseEnd_3615228 : Nat := 1856349639592686637523875

theorem tailTrace_3615228 : CollatzResearch.WordTrace tailWord_3615228 prefixEnd_3615228 1856349639592686637523875 := by
  unfold tailWord_3615228
  simp only [CollatzResearch.WordTrace]
  refine ⟨65929098873326931315627169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87905465164435908420836225 65929098873326931315627169)
  ·
    refine ⟨49446824154995198486720377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65929098873326931315627169 49446824154995198486720377)
    ·
      refine ⟨37085118116246398865040283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49446824154995198486720377 37085118116246398865040283)
      ·
        refine ⟨55627677174369598297560425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37085118116246398865040283 55627677174369598297560425)
        ·
          refine ⟨41720757880777198723170319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55627677174369598297560425 41720757880777198723170319)
          ·
            refine ⟨62581136821165798084755479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41720757880777198723170319 62581136821165798084755479)
            ·
              refine ⟨93871705231748697127133219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62581136821165798084755479 93871705231748697127133219)
              ·
                refine ⟨140807557847623045690699829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93871705231748697127133219 140807557847623045690699829)
                ·
                  refine ⟨13200708548214660533503109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140807557847623045690699829 13200708548214660533503109)
                  ·
                    refine ⟨2475132852790248850031833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13200708548214660533503109 2475132852790248850031833)
                    ·
                      refine ⟨1856349639592686637523875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475132852790248850031833 1856349639592686637523875)
                      ·
                        rfl

theorem cell23_3615228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_3615228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615228 prefixEnd_3615228 := by exact prefixLift 3615228
  have htrace : WordTrace (prefixWord ++ tailWord_3615228) baseStart_3615228 baseEnd_3615228 := by
    simpa [prefixWord, tailWord_3615228, baseEnd_3615228] using wordTrace_append hprefix tailTrace_3615228
  have hstable : (prefixWord ++ tailWord_3615228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615228).length < 2 ^ (prefixWord ++ tailWord_3615228).sum := by decide
  have hdescent : baseEnd_3615228 < baseStart_3615228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615231 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_3615231 : Nat := 118140960795 + 3615231 * 2 ^ 59
def prefixEnd_3615231 : Nat := 4983230072969 + 3 ^ 40 * 3615231 * 2
def baseEnd_3615231 : Nat := 1856351180034650125786361

theorem tailTrace_3615231 : CollatzResearch.WordTrace tailWord_3615231 prefixEnd_3615231 1856351180034650125786361 := by
  unfold tailWord_3615231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131858307165642994143613547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87905538110428662762409031 131858307165642994143613547)
  ·
    refine ⟨197787460748464491215420321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131858307165642994143613547 197787460748464491215420321)
    ·
      refine ⟨148340595561348368411565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197787460748464491215420321 148340595561348368411565241)
      ·
        refine ⟨111255446671011276308673931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148340595561348368411565241 111255446671011276308673931)
        ·
          refine ⟨166883170006516914463010897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111255446671011276308673931 166883170006516914463010897)
          ·
            refine ⟨125162377504887685847258173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166883170006516914463010897 125162377504887685847258173)
            ·
              refine ⟨46935891564332882192721815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125162377504887685847258173 46935891564332882192721815)
              ·
                refine ⟨70403837346499323289082723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46935891564332882192721815 70403837346499323289082723)
                ·
                  refine ⟨105605756019748984933624085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70403837346499323289082723 105605756019748984933624085)
                  ·
                    refine ⟨4950269813425733668763629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105605756019748984933624085 4950269813425733668763629)
                    ·
                      refine ⟨1856351180034650125786361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950269813425733668763629 1856351180034650125786361)
                      ·
                        rfl

theorem cell23_3615231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_3615231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615231 prefixEnd_3615231 := by exact prefixLift 3615231
  have htrace : WordTrace (prefixWord ++ tailWord_3615231) baseStart_3615231 baseEnd_3615231 := by
    simpa [prefixWord, tailWord_3615231, baseEnd_3615231] using wordTrace_append hprefix tailTrace_3615231
  have hstable : (prefixWord ++ tailWord_3615231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615231).length < 2 ^ (prefixWord ++ tailWord_3615231).sum := by decide
  have hdescent : baseEnd_3615231 < baseStart_3615231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615251 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 7]
def baseStart_3615251 : Nat := 118140960795 + 3615251 * 2 ^ 59
def prefixEnd_3615251 : Nat := 4983230072969 + 3 ^ 40 * 3615251 * 2
def baseEnd_3615251 : Nat := 206262383294193338615141

theorem tailTrace_3615251 : CollatzResearch.WordTrace tailWord_3615251 prefixEnd_3615251 206262383294193338615141 := by
  unfold tailWord_3615251
  simp only [CollatzResearch.WordTrace]
  refine ⟨131859036625570537559341607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87906024417047025039561071 131859036625570537559341607)
  ·
    refine ⟨197788554938355806339012411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131859036625570537559341607 197788554938355806339012411)
    ·
      refine ⟨296682832407533709508518617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197788554938355806339012411 296682832407533709508518617)
      ·
        refine ⟨222512124305650282131388963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296682832407533709508518617 222512124305650282131388963)
        ·
          refine ⟨333768186458475423197083445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222512124305650282131388963 333768186458475423197083445)
          ·
            refine ⟨31290767480482070924726573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333768186458475423197083445 31290767480482070924726573)
            ·
              refine ⟨11734037805180776596772465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31290767480482070924726573 11734037805180776596772465)
              ·
                refine ⟨8800528353885582447579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11734037805180776596772465 8800528353885582447579349)
                ·
                  refine ⟨206262383294193338615141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8800528353885582447579349 206262383294193338615141)
                  ·
                    rfl

theorem cell23_3615251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 7].length) (baseStart_3615251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615251 prefixEnd_3615251 := by exact prefixLift 3615251
  have htrace : WordTrace (prefixWord ++ tailWord_3615251) baseStart_3615251 baseEnd_3615251 := by
    simpa [prefixWord, tailWord_3615251, baseEnd_3615251] using wordTrace_append hprefix tailTrace_3615251
  have hstable : (prefixWord ++ tailWord_3615251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615251).length < 2 ^ (prefixWord ++ tailWord_3615251).sum := by decide
  have hdescent : baseEnd_3615251 < baseStart_3615251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615321 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3615321 : Nat := 118140960795 + 3615321 * 2 ^ 59
def prefixEnd_3615321 : Nat := 4983230072969 + 3 ^ 40 * 3615321 * 2
def baseEnd_3615321 : Nat := 1856397393293554773660947

theorem tailTrace_3615321 : CollatzResearch.WordTrace tailWord_3615321 prefixEnd_3615321 1856397393293554773660947 := by
  unfold tailWord_3615321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131861589735316939514389817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87907726490211293009593211 131861589735316939514389817)
  ·
    refine ⟨98896192301487704635792363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131861589735316939514389817 98896192301487704635792363)
    ·
      refine ⟨148344288452231556953688545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98896192301487704635792363 148344288452231556953688545)
      ·
        refine ⟨111258216339173667715266409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148344288452231556953688545 111258216339173667715266409)
        ·
          refine ⟨83443662254380250786449807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111258216339173667715266409 83443662254380250786449807)
          ·
            refine ⟨125165493381570376179674711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83443662254380250786449807 125165493381570376179674711)
            ·
              refine ⟨187748240072355564269512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125165493381570376179674711 187748240072355564269512067)
              ·
                refine ⟨281622360108533346404268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187748240072355564269512067 281622360108533346404268101)
                ·
                  refine ⟨52804192520350002450800269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281622360108533346404268101 52804192520350002450800269)
                  ·
                    refine ⟨19801572195131250919050101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52804192520350002450800269 19801572195131250919050101)
                    ·
                      refine ⟨1856397393293554773660947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19801572195131250919050101 1856397393293554773660947)
                      ·
                        rfl

theorem cell23_3615321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3615321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615321 prefixEnd_3615321 := by exact prefixLift 3615321
  have htrace : WordTrace (prefixWord ++ tailWord_3615321) baseStart_3615321 baseEnd_3615321 := by
    simpa [prefixWord, tailWord_3615321, baseEnd_3615321] using wordTrace_append hprefix tailTrace_3615321
  have hstable : (prefixWord ++ tailWord_3615321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615321).length < 2 ^ (prefixWord ++ tailWord_3615321).sum := by decide
  have hdescent : baseEnd_3615321 < baseStart_3615321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615328 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_3615328 : Nat := 118140960795 + 3615328 * 2 ^ 59
def prefixEnd_3615328 : Nat := 4983230072969 + 3 ^ 40 * 3615328 * 2
def baseEnd_3615328 : Nat := 618800329219378748757805

theorem tailTrace_3615328 : CollatzResearch.WordTrace tailWord_3615328 prefixEnd_3615328 618800329219378748757805 := by
  unfold tailWord_3615328
  simp only [CollatzResearch.WordTrace]
  refine ⟨65930922523145789854947319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87907896697527719806596425 65930922523145789854947319)
  ·
    refine ⟨98896383784718684782420979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65930922523145789854947319 98896383784718684782420979)
    ·
      refine ⟨148344575677078027173631469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98896383784718684782420979 148344575677078027173631469)
      ·
        refine ⟨55629215878904260190111801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148344575677078027173631469 55629215878904260190111801)
        ·
          refine ⟨41721911909178195142583851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55629215878904260190111801 41721911909178195142583851)
          ·
            refine ⟨62582867863767292713875777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41721911909178195142583851 62582867863767292713875777)
            ·
              refine ⟨46937150897825469535406833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62582867863767292713875777 46937150897825469535406833)
              ·
                refine ⟨35202863173369102151555125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46937150897825469535406833 35202863173369102151555125)
                ·
                  refine ⟨3300268422503353326708293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35202863173369102151555125 3300268422503353326708293)
                  ·
                    refine ⟨618800329219378748757805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300268422503353326708293 618800329219378748757805)
                    ·
                      rfl

theorem cell23_3615328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_3615328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615328 prefixEnd_3615328 := by exact prefixLift 3615328
  have htrace : WordTrace (prefixWord ++ tailWord_3615328) baseStart_3615328 baseEnd_3615328 := by
    simpa [prefixWord, tailWord_3615328, baseEnd_3615328] using wordTrace_append hprefix tailTrace_3615328
  have hstable : (prefixWord ++ tailWord_3615328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615328).length < 2 ^ (prefixWord ++ tailWord_3615328).sum := by decide
  have hdescent : baseEnd_3615328 < baseStart_3615328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615395 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 4, 3, 2]
def baseStart_3615395 : Nat := 118140960795 + 3615395 * 2 ^ 59
def prefixEnd_3615395 : Nat := 4983230072969 + 3 ^ 40 * 3615395 * 2
def baseEnd_3615395 : Nat := 1856435390861987484135607

theorem tailTrace_3615395 : CollatzResearch.WordTrace tailWord_3615395 prefixEnd_3615395 1856435390861987484135607 := by
  unfold tailWord_3615395
  simp only [CollatzResearch.WordTrace]
  refine ⟨131864288737048850152583639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87909525824699233435055759 131864288737048850152583639)
  ·
    refine ⟨197796433105573275228875459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131864288737048850152583639 197796433105573275228875459)
    ·
      refine ⟨296694649658359912843313189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197796433105573275228875459 296694649658359912843313189)
      ·
        refine ⟨55630246810942483658121223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296694649658359912843313189 55630246810942483658121223)
        ·
          refine ⟨83445370216413725487181835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55630246810942483658121223 83445370216413725487181835)
          ·
            refine ⟨125168055324620588230772753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83445370216413725487181835 125168055324620588230772753)
            ·
              refine ⟨93876041493465441173079565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125168055324620588230772753 93876041493465441173079565)
              ·
                refine ⟨35203515560049540439904837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93876041493465441173079565 35203515560049540439904837)
                ·
                  refine ⟨6600659167509288832482157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35203515560049540439904837 6600659167509288832482157)
                  ·
                    refine ⟨2475247187815983312180809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6600659167509288832482157 2475247187815983312180809)
                    ·
                      refine ⟨1856435390861987484135607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475247187815983312180809 1856435390861987484135607)
                      ·
                        rfl

theorem cell23_3615395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_3615395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615395 prefixEnd_3615395 := by exact prefixLift 3615395
  have htrace : WordTrace (prefixWord ++ tailWord_3615395) baseStart_3615395 baseEnd_3615395 := by
    simpa [prefixWord, tailWord_3615395, baseEnd_3615395] using wordTrace_append hprefix tailTrace_3615395
  have hstable : (prefixWord ++ tailWord_3615395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615395).length < 2 ^ (prefixWord ++ tailWord_3615395).sum := by decide
  have hdescent : baseEnd_3615395 < baseStart_3615395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615405 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3615405 : Nat := 118140960795 + 3615405 * 2 ^ 59
def prefixEnd_3615405 : Nat := 4983230072969 + 3 ^ 40 * 3615405 * 2
def baseEnd_3615405 : Nat := 618813508556177481670187

theorem tailTrace_3615405 : CollatzResearch.WordTrace tailWord_3615405 prefixEnd_3615405 618813508556177481670187 := by
  unfold tailWord_3615405
  simp only [CollatzResearch.WordTrace]
  refine ⟨131864653467012621860447669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87909768978008414573631779 131864653467012621860447669)
  ·
    refine ⟨12362311262532433299416969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131864653467012621860447669 12362311262532433299416969)
    ·
      refine ⟨9271733446899324974562727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12362311262532433299416969 9271733446899324974562727)
      ·
        refine ⟨13907600170348987461844091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271733446899324974562727 13907600170348987461844091)
        ·
          refine ⟨20861400255523481192766137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13907600170348987461844091 20861400255523481192766137)
          ·
            refine ⟨15646050191642610894574603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20861400255523481192766137 15646050191642610894574603)
            ·
              refine ⟨23469075287463916341861905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15646050191642610894574603 23469075287463916341861905)
              ·
                refine ⟨17601806465597937256396429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23469075287463916341861905 17601806465597937256396429)
                ·
                  refine ⟨6600677424599226471148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17601806465597937256396429 6600677424599226471148661)
                  ·
                    refine ⟨618813508556177481670187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6600677424599226471148661 618813508556177481670187)
                    ·
                      rfl

theorem cell23_3615405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3615405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615405 prefixEnd_3615405 := by exact prefixLift 3615405
  have htrace : WordTrace (prefixWord ++ tailWord_3615405) baseStart_3615405 baseEnd_3615405 := by
    simpa [prefixWord, tailWord_3615405, baseEnd_3615405] using wordTrace_append hprefix tailTrace_3615405
  have hstable : (prefixWord ++ tailWord_3615405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615405).length < 2 ^ (prefixWord ++ tailWord_3615405).sum := by decide
  have hdescent : baseEnd_3615405 < baseStart_3615405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615436 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3615436 : Nat := 118140960795 + 3615436 * 2 ^ 59
def prefixEnd_3615436 : Nat := 4983230072969 + 3 ^ 40 * 3615436 * 2
def baseEnd_3615436 : Nat := 1856456443568821823722919

theorem tailTrace_3615436 : CollatzResearch.WordTrace tailWord_3615436 prefixEnd_3615436 1856456443568821823722919 := by
  unfold tailWord_3615436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65932892064950157077413081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87910522753266876103217441 65932892064950157077413081)
  ·
    refine ⟨49449669048712617808059811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65932892064950157077413081 49449669048712617808059811)
    ·
      refine ⟨74174503573068926712089717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49449669048712617808059811 74174503573068926712089717)
      ·
        refine ⟨6953859709975211879258411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74174503573068926712089717 6953859709975211879258411)
        ·
          refine ⟨10430789564962817818887617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953859709975211879258411 10430789564962817818887617)
          ·
            refine ⟨7823092173722113364165713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10430789564962817818887617 7823092173722113364165713)
            ·
              refine ⟨5867319130291585023124285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7823092173722113364165713 5867319130291585023124285)
              ·
                refine ⟨2200244673859344383671607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5867319130291585023124285 2200244673859344383671607)
                ·
                  refine ⟨3300367010789016575507411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200244673859344383671607 3300367010789016575507411)
                  ·
                    refine ⟨4950550516183524863261117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300367010789016575507411 4950550516183524863261117)
                    ·
                      refine ⟨1856456443568821823722919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950550516183524863261117 1856456443568821823722919)
                      ·
                        rfl

theorem cell23_3615436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3615436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615436 prefixEnd_3615436 := by exact prefixLift 3615436
  have htrace : WordTrace (prefixWord ++ tailWord_3615436) baseStart_3615436 baseEnd_3615436 := by
    simpa [prefixWord, tailWord_3615436, baseEnd_3615436] using wordTrace_append hprefix tailTrace_3615436
  have hstable : (prefixWord ++ tailWord_3615436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615436).length < 2 ^ (prefixWord ++ tailWord_3615436).sum := by decide
  have hdescent : baseEnd_3615436 < baseStart_3615436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615448 : List Nat := [2, 1, 2, 2, 3, 3, 10]
def baseStart_3615448 : Nat := 118140960795 + 3615448 * 2 ^ 59
def prefixEnd_3615448 : Nat := 4983230072969 + 3 ^ 40 * 3615448 * 2
def baseEnd_3615448 : Nat := 22919291423909577491023

theorem tailTrace_3615448 : CollatzResearch.WordTrace tailWord_3615448 prefixEnd_3615448 22919291423909577491023 := by
  unfold tailWord_3615448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65933110902928420102131499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87910814537237893469508665 65933110902928420102131499)
  ·
    refine ⟨98899666354392630153197249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65933110902928420102131499 98899666354392630153197249)
    ·
      refine ⟨74174749765794472614897937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98899666354392630153197249 74174749765794472614897937)
      ·
        refine ⟨55631062324345854461173453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74174749765794472614897937 55631062324345854461173453)
        ·
          refine ⟨20861648371629695422940045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55631062324345854461173453 20861648371629695422940045)
          ·
            refine ⟨7823118139361135783602517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20861648371629695422940045 7823118139361135783602517)
            ·
              refine ⟨22919291423909577491023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7823118139361135783602517 22919291423909577491023)
              ·
                rfl

theorem cell23_3615448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 10].length) (baseStart_3615448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615448 prefixEnd_3615448 := by exact prefixLift 3615448
  have htrace : WordTrace (prefixWord ++ tailWord_3615448) baseStart_3615448 baseEnd_3615448 := by
    simpa [prefixWord, tailWord_3615448, baseEnd_3615448] using wordTrace_append hprefix tailTrace_3615448
  have hstable : (prefixWord ++ tailWord_3615448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615448).length < 2 ^ (prefixWord ++ tailWord_3615448).sum := by decide
  have hdescent : baseEnd_3615448 < baseStart_3615448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615459 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3615459 : Nat := 118140960795 + 3615459 * 2 ^ 59
def prefixEnd_3615459 : Nat := 4983230072969 + 3 ^ 40 * 3615459 * 2
def baseEnd_3615459 : Nat := 1856468253623875233735313

theorem tailTrace_3615459 : CollatzResearch.WordTrace tailWord_3615459 prefixEnd_3615459 1856468253623875233735313 := by
  unfold tailWord_3615459
  simp only [CollatzResearch.WordTrace]
  refine ⟨131866623008816989082913431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87911082005877992721942287 131866623008816989082913431)
  ·
    refine ⟨197799934513225483624370147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131866623008816989082913431 197799934513225483624370147)
    ·
      refine ⟨296699901769838225436555221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197799934513225483624370147 296699901769838225436555221)
      ·
        refine ⟨6953903947730583408669263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 296699901769838225436555221 6953903947730583408669263)
        ·
          refine ⟨10430855921595875113003895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953903947730583408669263 10430855921595875113003895)
          ·
            refine ⟨15646283882393812669505843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430855921595875113003895 15646283882393812669505843)
            ·
              refine ⟨23469425823590719004258765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15646283882393812669505843 23469425823590719004258765)
              ·
                refine ⟨8801034683846519626597037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23469425823590719004258765 8801034683846519626597037)
                ·
                  refine ⟨3300388006442444859973889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8801034683846519626597037 3300388006442444859973889)
                  ·
                    refine ⟨2475291004831833644980417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300388006442444859973889 2475291004831833644980417)
                    ·
                      refine ⟨1856468253623875233735313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475291004831833644980417 1856468253623875233735313)
                      ·
                        rfl

theorem cell23_3615459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3615459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615459 prefixEnd_3615459 := by exact prefixLift 3615459
  have htrace : WordTrace (prefixWord ++ tailWord_3615459) baseStart_3615459 baseEnd_3615459 := by
    simpa [prefixWord, tailWord_3615459, baseEnd_3615459] using wordTrace_append hprefix tailTrace_3615459
  have hstable : (prefixWord ++ tailWord_3615459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615459).length < 2 ^ (prefixWord ++ tailWord_3615459).sum := by decide
  have hdescent : baseEnd_3615459 < baseStart_3615459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615469 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_3615469 : Nat := 118140960795 + 3615469 * 2 ^ 59
def prefixEnd_3615469 : Nat := 4983230072969 + 3 ^ 40 * 3615469 * 2
def baseEnd_3615469 : Nat := 618824462810140064870089

theorem tailTrace_3615469 : CollatzResearch.WordTrace tailWord_3615469 prefixEnd_3615469 618824462810140064870089 := by
  unfold tailWord_3615469
  simp only [CollatzResearch.WordTrace]
  refine ⟨131866987738780760790777461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87911325159187173860518307 131866987738780760790777461)
  ·
    refine ⟨12362530100510696324135387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131866987738780760790777461 12362530100510696324135387)
    ·
      refine ⟨18543795150766044486203081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362530100510696324135387 18543795150766044486203081)
      ·
        refine ⟨13907846363074533364652311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18543795150766044486203081 13907846363074533364652311)
        ·
          refine ⟨20861769544611800046978467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13907846363074533364652311 20861769544611800046978467)
          ·
            refine ⟨31292654316917700070467701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20861769544611800046978467 31292654316917700070467701)
            ·
              refine ⟨2933686342211034381606347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31292654316917700070467701 2933686342211034381606347)
              ·
                refine ⟨4400529513316551572409521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933686342211034381606347 4400529513316551572409521)
                ·
                  refine ⟨3300397134987413679307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400529513316551572409521 3300397134987413679307141)
                  ·
                    refine ⟨618824462810140064870089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300397134987413679307141 618824462810140064870089)
                    ·
                      rfl

theorem cell23_3615469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_3615469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615469 prefixEnd_3615469 := by exact prefixLift 3615469
  have htrace : WordTrace (prefixWord ++ tailWord_3615469) baseStart_3615469 baseEnd_3615469 := by
    simpa [prefixWord, tailWord_3615469, baseEnd_3615469] using wordTrace_append hprefix tailTrace_3615469
  have hstable : (prefixWord ++ tailWord_3615469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615469).length < 2 ^ (prefixWord ++ tailWord_3615469).sum := by decide
  have hdescent : baseEnd_3615469 < baseStart_3615469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615492 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3615492 : Nat := 118140960795 + 3615492 * 2 ^ 59
def prefixEnd_3615492 : Nat := 4983230072969 + 3 ^ 40 * 3615492 * 2
def baseEnd_3615492 : Nat := 1856485198485473604622661

theorem tailTrace_3615492 : CollatzResearch.WordTrace tailWord_3615492 prefixEnd_3615492 1856485198485473604622661 := by
  unfold tailWord_3615492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65933913308848717859432365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87911884411798290479243153 65933913308848717859432365)
  ·
    refine ⟨24725217490818269197287137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65933913308848717859432365 24725217490818269197287137)
    ·
      refine ⟨18543913118113701897965353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24725217490818269197287137 18543913118113701897965353)
      ·
        refine ⟨13907934838585276423474015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18543913118113701897965353 13907934838585276423474015)
        ·
          refine ⟨20861902257877914635211023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13907934838585276423474015 20861902257877914635211023)
          ·
            refine ⟨31292853386816871952816535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20861902257877914635211023 31292853386816871952816535)
            ·
              refine ⟨46939280080225307929224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31292853386816871952816535 46939280080225307929224803)
              ·
                refine ⟨70408920120337961893837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46939280080225307929224803 70408920120337961893837205)
                ·
                  refine ⟨3300418130640841963773619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70408920120337961893837205 3300418130640841963773619)
                  ·
                    refine ⟨4950627195961262945660429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300418130640841963773619 4950627195961262945660429)
                    ·
                      refine ⟨1856485198485473604622661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950627195961262945660429 1856485198485473604622661)
                      ·
                        rfl

theorem cell23_3615492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3615492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615492 prefixEnd_3615492 := by exact prefixLift 3615492
  have htrace : WordTrace (prefixWord ++ tailWord_3615492) baseStart_3615492 baseEnd_3615492 := by
    simpa [prefixWord, tailWord_3615492, baseEnd_3615492] using wordTrace_append hprefix tailTrace_3615492
  have hstable : (prefixWord ++ tailWord_3615492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615492).length < 2 ^ (prefixWord ++ tailWord_3615492).sum := by decide
  have hdescent : baseEnd_3615492 < baseStart_3615492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615502 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3615502 : Nat := 118140960795 + 3615502 * 2 ^ 59
def prefixEnd_3615502 : Nat := 4983230072969 + 3 ^ 40 * 3615502 * 2
def baseEnd_3615502 : Nat := 1856490333292018565497615

theorem tailTrace_3615502 : CollatzResearch.WordTrace tailWord_3615502 prefixEnd_3615502 1856490333292018565497615 := by
  unfold tailWord_3615502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483523918457650928341095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87912127565107471617819173 16483523918457650928341095)
  ·
    refine ⟨24725285877686476392511643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16483523918457650928341095 24725285877686476392511643)
    ·
      refine ⟨37087928816529714588767465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24725285877686476392511643 37087928816529714588767465)
      ·
        refine ⟨27815946612397285941575599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37087928816529714588767465 27815946612397285941575599)
        ·
          refine ⟨41723919918595928912363399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27815946612397285941575599 41723919918595928912363399)
          ·
            refine ⟨62585879877893893368545099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41723919918595928912363399 62585879877893893368545099)
            ·
              refine ⟨93878819816840840052817649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62585879877893893368545099 93878819816840840052817649)
              ·
                refine ⟨70409114862630630039613237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93878819816840840052817649 70409114862630630039613237)
                ·
                  refine ⟨6600854518371621566213741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70409114862630630039613237 6600854518371621566213741)
                  ·
                    refine ⟨2475320444389358087330153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6600854518371621566213741 2475320444389358087330153)
                    ·
                      refine ⟨1856490333292018565497615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475320444389358087330153 1856490333292018565497615)
                      ·
                        rfl

theorem cell23_3615502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3615502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615502 prefixEnd_3615502 := by exact prefixLift 3615502
  have htrace : WordTrace (prefixWord ++ tailWord_3615502) baseStart_3615502 baseEnd_3615502 := by
    simpa [prefixWord, tailWord_3615502, baseEnd_3615502] using wordTrace_append hprefix tailTrace_3615502
  have hstable : (prefixWord ++ tailWord_3615502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615502).length < 2 ^ (prefixWord ++ tailWord_3615502).sum := by decide
  have hdescent : baseEnd_3615502 < baseStart_3615502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615515 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 8, 2]
def baseStart_3615515 : Nat := 118140960795 + 3615515 * 2 ^ 59
def prefixEnd_3615515 : Nat := 4983230072969 + 3 ^ 40 * 3615515 * 2
def baseEnd_3615515 : Nat := 1856497008540527014635055

theorem tailTrace_3615515 : CollatzResearch.WordTrace tailWord_3615515 prefixEnd_3615515 1856497008540527014635055 := by
  unfold tailWord_3615515
  simp only [CollatzResearch.WordTrace]
  refine ⟨131868665496614110646951999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87912443664409407097967999 131868665496614110646951999)
  ·
    refine ⟨197802998244921165970427999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131868665496614110646951999 197802998244921165970427999)
    ·
      refine ⟨296704497367381748955641999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197802998244921165970427999 296704497367381748955641999)
      ·
        refine ⟨445056746051072623433462999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296704497367381748955641999 445056746051072623433462999)
        ·
          refine ⟨667585119076608935150194499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445056746051072623433462999 667585119076608935150194499)
          ·
            refine ⟨1001377678614913402725291749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667585119076608935150194499 1001377678614913402725291749)
            ·
              refine ⟨187758314740296263010992203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1001377678614913402725291749 187758314740296263010992203)
              ·
                refine ⟨281637472110444394516488305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187758314740296263010992203 281637472110444394516488305)
                ·
                  refine ⟨211228104082833295887366229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281637472110444394516488305 211228104082833295887366229)
                  ·
                    refine ⟨2475329344720702686180073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 211228104082833295887366229 2475329344720702686180073)
                    ·
                      refine ⟨1856497008540527014635055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475329344720702686180073 1856497008540527014635055)
                      ·
                        rfl

theorem cell23_3615515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8, 2].length) (baseStart_3615515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615515 prefixEnd_3615515 := by exact prefixLift 3615515
  have htrace : WordTrace (prefixWord ++ tailWord_3615515) baseStart_3615515 baseEnd_3615515 := by
    simpa [prefixWord, tailWord_3615515, baseEnd_3615515] using wordTrace_append hprefix tailTrace_3615515
  have hstable : (prefixWord ++ tailWord_3615515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615515).length < 2 ^ (prefixWord ++ tailWord_3615515).sum := by decide
  have hdescent : baseEnd_3615515 < baseStart_3615515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615532 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_3615532 : Nat := 118140960795 + 3615532 * 2 ^ 59
def prefixEnd_3615532 : Nat := 4983230072969 + 3 ^ 40 * 3615532 * 2
def baseEnd_3615532 : Nat := 1856505737711653448122477

theorem tailTrace_3615532 : CollatzResearch.WordTrace tailWord_3615532 prefixEnd_3615532 1856505737711653448122477 := by
  unfold tailWord_3615532
  simp only [CollatzResearch.WordTrace]
  refine ⟨65934642768776261275160425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87912857025035015033547233 65934642768776261275160425)
  ·
    refine ⟨49450982076582195956370319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65934642768776261275160425 49450982076582195956370319)
    ·
      refine ⟨74176473114873293934555479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49450982076582195956370319 74176473114873293934555479)
      ·
        refine ⟨111264709672309940901833219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74176473114873293934555479 111264709672309940901833219)
        ·
          refine ⟨166897064508464911352749829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111264709672309940901833219 166897064508464911352749829)
          ·
            refine ⟨31293199595337170878640593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166897064508464911352749829 31293199595337170878640593)
            ·
              refine ⟨23469899696502878158980445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31293199595337170878640593 23469899696502878158980445)
              ·
                refine ⟨8801212386188579309617667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23469899696502878158980445 8801212386188579309617667)
                ·
                  refine ⟨13201818579282868964426501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8801212386188579309617667 13201818579282868964426501)
                  ·
                    refine ⟨2475340983615537930829969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13201818579282868964426501 2475340983615537930829969)
                    ·
                      refine ⟨1856505737711653448122477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475340983615537930829969 1856505737711653448122477)
                      ·
                        rfl

theorem cell23_3615532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_3615532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615532 prefixEnd_3615532 := by exact prefixLift 3615532
  have htrace : WordTrace (prefixWord ++ tailWord_3615532) baseStart_3615532 baseEnd_3615532 := by
    simpa [prefixWord, tailWord_3615532, baseEnd_3615532] using wordTrace_append hprefix tailTrace_3615532
  have hstable : (prefixWord ++ tailWord_3615532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615532).length < 2 ^ (prefixWord ++ tailWord_3615532).sum := by decide
  have hdescent : baseEnd_3615532 < baseStart_3615532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615602 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3615602 : Nat := 118140960795 + 3615602 * 2 ^ 59
def prefixEnd_3615602 : Nat := 4983230072969 + 3 ^ 40 * 3615602 * 2
def baseEnd_3615602 : Nat := 618847227119156058082385

theorem tailTrace_3615602 : CollatzResearch.WordTrace tailWord_3615602 prefixEnd_3615602 618847227119156058082385 := by
  unfold tailWord_3615602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967959661824731126342265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87914559098199283003579373 32967959661824731126342265)
  ·
    refine ⟨24725969746368548344756699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32967959661824731126342265 24725969746368548344756699)
    ·
      refine ⟨37088954619552822517135049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24725969746368548344756699 37088954619552822517135049)
      ·
        refine ⟨27816715964664616887851287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37088954619552822517135049 27816715964664616887851287)
        ·
          refine ⟨41725073946996925331776931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27816715964664616887851287 41725073946996925331776931)
          ·
            refine ⟨62587610920495387997665397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41725073946996925331776931 62587610920495387997665397)
            ·
              refine ⟨5867588523796442624781131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62587610920495387997665397 5867588523796442624781131)
              ·
                refine ⟨8801382785694663937171697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5867588523796442624781131 8801382785694663937171697)
                ·
                  refine ⟨6601037089270997952878773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8801382785694663937171697 6601037089270997952878773)
                  ·
                    refine ⟨618847227119156058082385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6601037089270997952878773 618847227119156058082385)
                    ·
                      rfl

theorem cell23_3615602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3615602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615602 prefixEnd_3615602 := by exact prefixLift 3615602
  have htrace : WordTrace (prefixWord ++ tailWord_3615602) baseStart_3615602 baseEnd_3615602 := by
    simpa [prefixWord, tailWord_3615602, baseEnd_3615602] using wordTrace_append hprefix tailTrace_3615602
  have hstable : (prefixWord ++ tailWord_3615602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615602).length < 2 ^ (prefixWord ++ tailWord_3615602).sum := by decide
  have hdescent : baseEnd_3615602 < baseStart_3615602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615606 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3615606 : Nat := 118140960795 + 3615606 * 2 ^ 59
def prefixEnd_3615606 : Nat := 4983230072969 + 3 ^ 40 * 3615606 * 2
def baseEnd_3615606 : Nat := 206282637253342906510793

theorem tailTrace_3615606 : CollatzResearch.WordTrace tailWord_3615606 prefixEnd_3615606 206282637253342906510793 := by
  unfold tailWord_3615606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241999033705277074282167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87914656359522955459009781 8241999033705277074282167)
  ·
    refine ⟨12362998550557915611423251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241999033705277074282167 12362998550557915611423251)
    ·
      refine ⟨18544497825836873417134877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362998550557915611423251 18544497825836873417134877)
      ·
        refine ⟨6954186684688827531425579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18544497825836873417134877 6954186684688827531425579)
        ·
          refine ⟨10431280027033241297138369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954186684688827531425579 10431280027033241297138369)
          ·
            refine ⟨7823460020274930972853777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10431280027033241297138369 7823460020274930972853777)
            ·
              refine ⟨5867595015206198229640333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7823460020274930972853777 5867595015206198229640333)
              ·
                refine ⟨2200348130702324336115125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5867595015206198229640333 2200348130702324336115125)
                ·
                  refine ⟨206282637253342906510793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200348130702324336115125 206282637253342906510793)
                  ·
                    rfl

theorem cell23_3615606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3615606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615606 prefixEnd_3615606 := by exact prefixLift 3615606
  have htrace : WordTrace (prefixWord ++ tailWord_3615606) baseStart_3615606 baseEnd_3615606 := by
    simpa [prefixWord, tailWord_3615606, baseEnd_3615606] using wordTrace_append hprefix tailTrace_3615606
  have hstable : (prefixWord ++ tailWord_3615606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615606).length < 2 ^ (prefixWord ++ tailWord_3615606).sum := by decide
  have hdescent : baseEnd_3615606 < baseStart_3615606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615649 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3615649 : Nat := 118140960795 + 3615649 * 2 ^ 59
def prefixEnd_3615649 : Nat := 4983230072969 + 3 ^ 40 * 3615649 * 2
def baseEnd_3615649 : Nat := 618855271649409830119813

theorem tailTrace_3615649 : CollatzResearch.WordTrace tailWord_3615649 prefixEnd_3615649 618855271649409830119813 := by
  unfold tailWord_3615649
  simp only [CollatzResearch.WordTrace]
  refine ⟨131873552878128651532330001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87915701918752434354886667 131873552878128651532330001)
  ·
    refine ⟨98905164658596488649247501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131873552878128651532330001 98905164658596488649247501)
    ·
      refine ⟨37089436746973683243467813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98905164658596488649247501 37089436746973683243467813)
      ·
        refine ⟨6954269390057565608150215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37089436746973683243467813 6954269390057565608150215)
        ·
          refine ⟨10431404085086348412225323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954269390057565608150215 10431404085086348412225323)
          ·
            refine ⟨15647106127629522618337985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431404085086348412225323 15647106127629522618337985)
            ·
              refine ⟨11735329595722141963753489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647106127629522618337985 11735329595722141963753489)
              ·
                refine ⟨8801497196791606472815117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11735329595722141963753489 8801497196791606472815117)
                ·
                  refine ⟨3300561448796852427305669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8801497196791606472815117 3300561448796852427305669)
                  ·
                    refine ⟨618855271649409830119813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3300561448796852427305669 618855271649409830119813)
                    ·
                      rfl

theorem cell23_3615649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3615649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615649 prefixEnd_3615649 := by exact prefixLift 3615649
  have htrace : WordTrace (prefixWord ++ tailWord_3615649) baseStart_3615649 baseEnd_3615649 := by
    simpa [prefixWord, tailWord_3615649, baseEnd_3615649] using wordTrace_append hprefix tailTrace_3615649
  have hstable : (prefixWord ++ tailWord_3615649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615649).length < 2 ^ (prefixWord ++ tailWord_3615649).sum := by decide
  have hdescent : baseEnd_3615649 < baseStart_3615649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615692 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_3615692 : Nat := 118140960795 + 3615692 * 2 ^ 59
def prefixEnd_3615692 : Nat := 4983230072969 + 3 ^ 40 * 3615692 * 2
def baseEnd_3615692 : Nat := 618862631538790940707247

theorem tailTrace_3615692 : CollatzResearch.WordTrace tailWord_3615692 prefixEnd_3615692 618862631538790940707247 := by
  unfold tailWord_3615692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65937560608486434938072665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87916747477981913250763553 65937560608486434938072665)
  ·
    refine ⟨49453170456364826203554499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65937560608486434938072665 49453170456364826203554499)
    ·
      refine ⟨74179755684547239305331749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49453170456364826203554499 74179755684547239305331749)
      ·
        refine ⟨13908704190852607369749703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74179755684547239305331749 13908704190852607369749703)
        ·
          refine ⟨20863056286278911054624555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908704190852607369749703 20863056286278911054624555)
          ·
            refine ⟨31294584429418366581936833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20863056286278911054624555 31294584429418366581936833)
            ·
              refine ⟨23470938322063774936452625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31294584429418366581936833 23470938322063774936452625)
              ·
                refine ⟨17603203741547831202339469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23470938322063774936452625 17603203741547831202339469)
                ·
                  refine ⟨6601201403080436700877301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17603203741547831202339469 6601201403080436700877301)
                  ·
                    refine ⟨618862631538790940707247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6601201403080436700877301 618862631538790940707247)
                    ·
                      rfl

theorem cell23_3615692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_3615692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615692 prefixEnd_3615692 := by exact prefixLift 3615692
  have htrace : WordTrace (prefixWord ++ tailWord_3615692) baseStart_3615692 baseEnd_3615692 := by
    simpa [prefixWord, tailWord_3615692, baseEnd_3615692] using wordTrace_append hprefix tailTrace_3615692
  have hstable : (prefixWord ++ tailWord_3615692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615692).length < 2 ^ (prefixWord ++ tailWord_3615692).sum := by decide
  have hdescent : baseEnd_3615692 < baseStart_3615692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615709 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3615709 : Nat := 118140960795 + 3615709 * 2 ^ 59
def prefixEnd_3615709 : Nat := 4983230072969 + 3 ^ 40 * 3615709 * 2
def baseEnd_3615709 : Nat := 618865541262499751869721

theorem tailTrace_3615709 : CollatzResearch.WordTrace tailWord_3615709 prefixEnd_3615709 618865541262499751869721 := by
  unfold tailWord_3615709
  simp only [CollatzResearch.WordTrace]
  refine ⟨131875741257911281779514181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87917160838607521186342787 131875741257911281779514181)
  ·
    refine ⟨24726701485858365333658909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131875741257911281779514181 24726701485858365333658909)
    ·
      refine ⟨9272513057196887000122091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24726701485858365333658909 9272513057196887000122091)
      ·
        refine ⟨13908769585795330500183137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272513057196887000122091 13908769585795330500183137)
        ·
          refine ⟨10431577189346497875137353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13908769585795330500183137 10431577189346497875137353)
          ·
            refine ⟨7823682892009873406353015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10431577189346497875137353 7823682892009873406353015)
            ·
              refine ⟨11735524338014810109529523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823682892009873406353015 11735524338014810109529523)
              ·
                refine ⟨17603286507022215164294285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735524338014810109529523 17603286507022215164294285)
                ·
                  refine ⟨6601232440133330686610357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17603286507022215164294285 6601232440133330686610357)
                  ·
                    refine ⟨618865541262499751869721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6601232440133330686610357 618865541262499751869721)
                    ·
                      rfl

theorem cell23_3615709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3615709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615709 prefixEnd_3615709 := by exact prefixLift 3615709
  have htrace : WordTrace (prefixWord ++ tailWord_3615709) baseStart_3615709 baseEnd_3615709 := by
    simpa [prefixWord, tailWord_3615709, baseEnd_3615709] using wordTrace_append hprefix tailTrace_3615709
  have hstable : (prefixWord ++ tailWord_3615709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615709).length < 2 ^ (prefixWord ++ tailWord_3615709).sum := by decide
  have hdescent : baseEnd_3615709 < baseStart_3615709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615722 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3615722 : Nat := 118140960795 + 3615722 * 2 ^ 59
def prefixEnd_3615722 : Nat := 4983230072969 + 3 ^ 40 * 3615722 * 2
def baseEnd_3615722 : Nat := 618867766345335901582201

theorem tailTrace_3615722 : CollatzResearch.WordTrace tailWord_3615722 prefixEnd_3615722 618867766345335901582201 := by
  unfold tailWord_3615722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969053851716046249934355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87917476937909456666491613 32969053851716046249934355)
  ·
    refine ⟨49453580777574069374901533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969053851716046249934355 49453580777574069374901533)
    ·
      refine ⟨18545092791590276015588075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49453580777574069374901533 18545092791590276015588075)
      ·
        refine ⟨27817639187385414023382113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18545092791590276015588075 27817639187385414023382113)
        ·
          refine ⟨20863229390539060517536585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27817639187385414023382113 20863229390539060517536585)
          ·
            refine ⟨15647422042904295388152439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20863229390539060517536585 15647422042904295388152439)
            ·
              refine ⟨23471133064356443082228659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15647422042904295388152439 23471133064356443082228659)
              ·
                refine ⟨35206699596534664623342989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23471133064356443082228659 35206699596534664623342989)
                ·
                  refine ⟨13202512348700499233753621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35206699596534664623342989 13202512348700499233753621)
                  ·
                    refine ⟨618867766345335901582201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13202512348700499233753621 618867766345335901582201)
                    ·
                      rfl

theorem cell23_3615722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3615722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615722 prefixEnd_3615722 := by exact prefixLift 3615722
  have htrace : WordTrace (prefixWord ++ tailWord_3615722) baseStart_3615722 baseEnd_3615722 := by
    simpa [prefixWord, tailWord_3615722, baseEnd_3615722] using wordTrace_append hprefix tailTrace_3615722
  have hstable : (prefixWord ++ tailWord_3615722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615722).length < 2 ^ (prefixWord ++ tailWord_3615722).sum := by decide
  have hdescent : baseEnd_3615722 < baseStart_3615722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615740 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_3615740 : Nat := 118140960795 + 3615740 * 2 ^ 59
def prefixEnd_3615740 : Nat := 4983230072969 + 3 ^ 40 * 3615740 * 2
def baseEnd_3615740 : Nat := 1856612541687788634321521

theorem tailTrace_3615740 : CollatzResearch.WordTrace tailWord_3615740 prefixEnd_3615740 1856612541687788634321521 := by
  unfold tailWord_3615740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65938435960399487036946337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87917914613865982715928449 65938435960399487036946337)
  ·
    refine ⟨49453826970299615277709753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65938435960399487036946337 49453826970299615277709753)
    ·
      refine ⟨37090370227724711458282315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49453826970299615277709753 37090370227724711458282315)
      ·
        refine ⟨55635555341587067187423473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37090370227724711458282315 55635555341587067187423473)
        ·
          refine ⟨41726666506190300390567605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55635555341587067187423473 41726666506190300390567605)
          ·
            refine ⟨3911874984955340661615713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41726666506190300390567605 3911874984955340661615713)
            ·
              refine ⟨2933906238716505496211785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911874984955340661615713 2933906238716505496211785)
              ·
                refine ⟨2200429679037379122158839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933906238716505496211785 2200429679037379122158839)
                ·
                  refine ⟨3300644518556068683238259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200429679037379122158839 3300644518556068683238259)
                  ·
                    refine ⟨4950966777834103024857389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300644518556068683238259 4950966777834103024857389)
                    ·
                      refine ⟨1856612541687788634321521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4950966777834103024857389 1856612541687788634321521)
                      ·
                        rfl

theorem cell23_3615740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_3615740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615740 prefixEnd_3615740 := by exact prefixLift 3615740
  have htrace : WordTrace (prefixWord ++ tailWord_3615740) baseStart_3615740 baseEnd_3615740 := by
    simpa [prefixWord, tailWord_3615740, baseEnd_3615740] using wordTrace_append hprefix tailTrace_3615740
  have hstable : (prefixWord ++ tailWord_3615740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615740).length < 2 ^ (prefixWord ++ tailWord_3615740).sum := by decide
  have hdescent : baseEnd_3615740 < baseStart_3615740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615752 : List Nat := [2, 1, 3, 2, 1, 3, 3, 8]
def baseStart_3615752 : Nat := 118140960795 + 3615752 * 2 ^ 59
def prefixEnd_3615752 : Nat := 4983230072969 + 3 ^ 40 * 3615752 * 2
def baseEnd_3615752 : Nat := 68763655683542318050795

theorem tailTrace_3615752 : CollatzResearch.WordTrace tailWord_3615752 prefixEnd_3615752 68763655683542318050795 := by
  unfold tailWord_3615752
  simp only [CollatzResearch.WordTrace]
  refine ⟨65938654798377750061664755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87918206397837000082219673 65938654798377750061664755)
  ·
    refine ⟨98907982197566625092497133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65938654798377750061664755 98907982197566625092497133)
    ·
      refine ⟨37090493324087484409686425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98907982197566625092497133 37090493324087484409686425)
      ·
        refine ⟨27817869993065613307264819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37090493324087484409686425 27817869993065613307264819)
        ·
          refine ⟨41726804989598419960897229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27817869993065613307264819 41726804989598419960897229)
          ·
            refine ⟨15647551871099407485336461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41726804989598419960897229 15647551871099407485336461)
            ·
              refine ⟨5867831951662277807001173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15647551871099407485336461 5867831951662277807001173)
              ·
                refine ⟨68763655683542318050795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5867831951662277807001173 68763655683542318050795)
                ·
                  rfl

theorem cell23_3615752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 8].length) (baseStart_3615752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615752 prefixEnd_3615752 := by exact prefixLift 3615752
  have htrace : WordTrace (prefixWord ++ tailWord_3615752) baseStart_3615752 baseEnd_3615752 := by
    simpa [prefixWord, tailWord_3615752, baseEnd_3615752] using wordTrace_append hprefix tailTrace_3615752
  have hstable : (prefixWord ++ tailWord_3615752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615752).length < 2 ^ (prefixWord ++ tailWord_3615752).sum := by decide
  have hdescent : baseEnd_3615752 < baseStart_3615752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615779 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3]
def baseStart_3615779 : Nat := 118140960795 + 3615779 * 2 ^ 59
def prefixEnd_3615779 : Nat := 4983230072969 + 3 ^ 40 * 3615779 * 2
def baseEnd_3615779 : Nat := 1856632567433313981733841

theorem tailTrace_3615779 : CollatzResearch.WordTrace tailWord_3615779 prefixEnd_3615779 1856632567433313981733841 := by
  unfold tailWord_3615779
  simp only [CollatzResearch.WordTrace]
  refine ⟨131878294367657683734562391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87918862911771789156374927 131878294367657683734562391)
  ·
    refine ⟨197817441551486525601843587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131878294367657683734562391 197817441551486525601843587)
    ·
      refine ⟨296726162327229788402765381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197817441551486525601843587 296726162327229788402765381)
      ·
        refine ⟨55636155436355585325518509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296726162327229788402765381 55636155436355585325518509)
        ·
          refine ⟨20863558288633344497069441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55636155436355585325518509 20863558288633344497069441)
          ·
            refine ⟨15647668716475008372802081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20863558288633344497069441 15647668716475008372802081)
            ·
              refine ⟨11735751537356256279601561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647668716475008372802081 11735751537356256279601561)
              ·
                refine ⟨8801813653017192209701171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11735751537356256279601561 8801813653017192209701171)
                ·
                  refine ⟨13202720479525788314551757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8801813653017192209701171 13202720479525788314551757)
                  ·
                    refine ⟨4951020179822170617956909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13202720479525788314551757 4951020179822170617956909)
                    ·
                      refine ⟨1856632567433313981733841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951020179822170617956909 1856632567433313981733841)
                      ·
                        rfl

theorem cell23_3615779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_3615779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615779 prefixEnd_3615779 := by exact prefixLift 3615779
  have htrace : WordTrace (prefixWord ++ tailWord_3615779) baseStart_3615779 baseEnd_3615779 := by
    simpa [prefixWord, tailWord_3615779, baseEnd_3615779] using wordTrace_append hprefix tailTrace_3615779
  have hstable : (prefixWord ++ tailWord_3615779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615779).length < 2 ^ (prefixWord ++ tailWord_3615779).sum := by decide
  have hdescent : baseEnd_3615779 < baseStart_3615779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615780 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3615780 : Nat := 118140960795 + 3615780 * 2 ^ 59
def prefixEnd_3615780 : Nat := 4983230072969 + 3 ^ 40 * 3615780 * 2
def baseEnd_3615780 : Nat := 1856633080913968477821337

theorem tailTrace_3615780 : CollatzResearch.WordTrace tailWord_3615780 prefixEnd_3615780 1856633080913968477821337 := by
  unfold tailWord_3615780
  simp only [CollatzResearch.WordTrace]
  refine ⟨65939165420327030452674397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87918887227102707270232529 65939165420327030452674397)
  ·
    refine ⟨24727187032622636419752899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65939165420327030452674397 24727187032622636419752899)
    ·
      refine ⟨37090780548933954629629349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727187032622636419752899 37090780548933954629629349)
      ·
        refine ⟨6954521352925116493055503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37090780548933954629629349 6954521352925116493055503)
        ·
          refine ⟨10431782029387674739583255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954521352925116493055503 10431782029387674739583255)
          ·
            refine ⟨15647673044081512109374883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10431782029387674739583255 15647673044081512109374883)
            ·
              refine ⟨23471509566122268164062325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15647673044081512109374883 23471509566122268164062325)
              ·
                refine ⟨2200454021823962640380843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23471509566122268164062325 2200454021823962640380843)
                ·
                  refine ⟨3300681032735943960571265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200454021823962640380843 3300681032735943960571265)
                  ·
                    refine ⟨2475510774551957970428449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300681032735943960571265 2475510774551957970428449)
                    ·
                      refine ⟨1856633080913968477821337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475510774551957970428449 1856633080913968477821337)
                      ·
                        rfl

theorem cell23_3615780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3615780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615780 prefixEnd_3615780 := by exact prefixLift 3615780
  have htrace : WordTrace (prefixWord ++ tailWord_3615780) baseStart_3615780 baseEnd_3615780 := by
    simpa [prefixWord, tailWord_3615780, baseEnd_3615780] using wordTrace_append hprefix tailTrace_3615780
  have hstable : (prefixWord ++ tailWord_3615780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615780).length < 2 ^ (prefixWord ++ tailWord_3615780).sum := by decide
  have hdescent : baseEnd_3615780 < baseStart_3615780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615783 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3615783 : Nat := 118140960795 + 3615783 * 2 ^ 59
def prefixEnd_3615783 : Nat := 4983230072969 + 3 ^ 40 * 3615783 * 2
def baseEnd_3615783 : Nat := 1856634621355931966083823

theorem tailTrace_3615783 : CollatzResearch.WordTrace tailWord_3615783 prefixEnd_3615783 1856634621355931966083823 := by
  unfold tailWord_3615783
  simp only [CollatzResearch.WordTrace]
  refine ⟨131878440259643192417708003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87918960173095461611805335 131878440259643192417708003)
  ·
    refine ⟨197817660389464788626562005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131878440259643192417708003 197817660389464788626562005)
    ·
      refine ⟨4636351415378080983435047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 197817660389464788626562005 4636351415378080983435047)
      ·
        refine ⟨6954527123067121475152571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636351415378080983435047 6954527123067121475152571)
        ·
          refine ⟨10431790684600682212728857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954527123067121475152571 10431790684600682212728857)
          ·
            refine ⟨7823843013450511659546643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10431790684600682212728857 7823843013450511659546643)
            ·
              refine ⟨11735764520175767489319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823843013450511659546643 11735764520175767489319965)
              ·
                refine ⟨4400911695065912808494987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11735764520175767489319965 4400911695065912808494987)
                ·
                  refine ⟨6601367542598869212742481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400911695065912808494987 6601367542598869212742481)
                  ·
                    refine ⟨4951025656949151909556861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601367542598869212742481 4951025656949151909556861)
                    ·
                      refine ⟨1856634621355931966083823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951025656949151909556861 1856634621355931966083823)
                      ·
                        rfl

theorem cell23_3615783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3615783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615783 prefixEnd_3615783 := by exact prefixLift 3615783
  have htrace : WordTrace (prefixWord ++ tailWord_3615783) baseStart_3615783 baseEnd_3615783 := by
    simpa [prefixWord, tailWord_3615783, baseEnd_3615783] using wordTrace_append hprefix tailTrace_3615783
  have hstable : (prefixWord ++ tailWord_3615783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615783).length < 2 ^ (prefixWord ++ tailWord_3615783).sum := by decide
  have hdescent : baseEnd_3615783 < baseStart_3615783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615802 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_3615802 : Nat := 118140960795 + 3615802 * 2 ^ 59
def prefixEnd_3615802 : Nat := 4983230072969 + 3 ^ 40 * 3615802 * 2
def baseEnd_3615802 : Nat := 1856644377488367391746235

theorem tailTrace_3615802 : CollatzResearch.WordTrace tailWord_3615802 prefixEnd_3615802 1856644377488367391746235 := by
  unfold tailWord_3615802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969783311643589665662415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87919422164382905775099773 32969783311643589665662415)
  ·
    refine ⟨49454674967465384498493623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969783311643589665662415 49454674967465384498493623)
    ·
      refine ⟨74182012451198076747740435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49454674967465384498493623 74182012451198076747740435)
      ·
        refine ⟨111273018676797115121610653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74182012451198076747740435 111273018676797115121610653)
        ·
          refine ⟨41727382003798918170603995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111273018676797115121610653 41727382003798918170603995)
          ·
            refine ⟨62591073005698377255905993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41727382003798918170603995 62591073005698377255905993)
            ·
              refine ⟨46943304754273782941929495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62591073005698377255905993 46943304754273782941929495)
              ·
                refine ⟨70414957131410674412894243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46943304754273782941929495 70414957131410674412894243)
                ·
                  refine ⟨105622435697116011619341365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70414957131410674412894243 105622435697116011619341365)
                  ·
                    refine ⟨9902103346604626089313253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105622435697116011619341365 9902103346604626089313253)
                    ·
                      refine ⟨1856644377488367391746235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9902103346604626089313253 1856644377488367391746235)
                      ·
                        rfl

theorem cell23_3615802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_3615802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615802 prefixEnd_3615802 := by exact prefixLift 3615802
  have htrace : WordTrace (prefixWord ++ tailWord_3615802) baseStart_3615802 baseEnd_3615802 := by
    simpa [prefixWord, tailWord_3615802, baseEnd_3615802] using wordTrace_append hprefix tailTrace_3615802
  have hstable : (prefixWord ++ tailWord_3615802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615802).length < 2 ^ (prefixWord ++ tailWord_3615802).sum := by decide
  have hdescent : baseEnd_3615802 < baseStart_3615802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615836 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3615836 : Nat := 118140960795 + 3615836 * 2 ^ 59
def prefixEnd_3615836 : Nat := 4983230072969 + 3 ^ 40 * 3615836 * 2
def baseEnd_3615836 : Nat := 1856661835830620258721079

theorem tailTrace_3615836 : CollatzResearch.WordTrace tailWord_3615836 prefixEnd_3615836 1856661835830620258721079 := by
  unfold tailWord_3615836
  simp only [CollatzResearch.WordTrace]
  refine ⟨65940186664225591234693681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87920248885634121646258241 65940186664225591234693681)
  ·
    refine ⟨49455139998169193426020261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65940186664225591234693681 49455139998169193426020261)
    ·
      refine ⟨9272838749656723767378799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49455139998169193426020261 9272838749656723767378799)
      ·
        refine ⟨13909258124485085651068199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272838749656723767378799 13909258124485085651068199)
        ·
          refine ⟨20863887186727628476602299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909258124485085651068199 20863887186727628476602299)
          ·
            refine ⟨31295830780091442714903449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20863887186727628476602299 31295830780091442714903449)
            ·
              refine ⟨23471873085068582036177587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31295830780091442714903449 23471873085068582036177587)
              ·
                refine ⟨35207809627602873054266381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23471873085068582036177587 35207809627602873054266381)
                ·
                  refine ⟨13202928610351077395349893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35207809627602873054266381 13202928610351077395349893)
                  ·
                    refine ⟨2475549114440827011628105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13202928610351077395349893 2475549114440827011628105)
                    ·
                      refine ⟨1856661835830620258721079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475549114440827011628105 1856661835830620258721079)
                      ·
                        rfl

theorem cell23_3615836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3615836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615836 prefixEnd_3615836 := by exact prefixLift 3615836
  have htrace : WordTrace (prefixWord ++ tailWord_3615836) baseStart_3615836 baseEnd_3615836 := by
    simpa [prefixWord, tailWord_3615836, baseEnd_3615836] using wordTrace_append hprefix tailTrace_3615836
  have hstable : (prefixWord ++ tailWord_3615836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615836).length < 2 ^ (prefixWord ++ tailWord_3615836).sum := by decide
  have hdescent : baseEnd_3615836 < baseStart_3615836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615852 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3615852 : Nat := 118140960795 + 3615852 * 2 ^ 59
def prefixEnd_3615852 : Nat := 4983230072969 + 3 ^ 40 * 3615852 * 2
def baseEnd_3615852 : Nat := 1856670051521092196121005

theorem tailTrace_3615852 : CollatzResearch.WordTrace tailWord_3615852 prefixEnd_3615852 1856670051521092196121005 := by
  unfold tailWord_3615852
  simp only [CollatzResearch.WordTrace]
  refine ⟨65940478448196608600984905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87920637930928811467979873 65940478448196608600984905)
  ·
    refine ⟨49455358836147456450738679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65940478448196608600984905 49455358836147456450738679)
    ·
      refine ⟨74183038254221184676108019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49455358836147456450738679 74183038254221184676108019)
      ·
        refine ⟨111274557381331777014162029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74183038254221184676108019 111274557381331777014162029)
        ·
          refine ⟨41727959017999416380310761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111274557381331777014162029 41727959017999416380310761)
          ·
            refine ⟨31295969263499562285233071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41727959017999416380310761 31295969263499562285233071)
            ·
              refine ⟨46943953895249343427849607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31295969263499562285233071 46943953895249343427849607)
              ·
                refine ⟨70415930842874015141774411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46943953895249343427849607 70415930842874015141774411)
                ·
                  refine ⟨105623896264311022712661617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70415930842874015141774411 105623896264311022712661617)
                  ·
                    refine ⟨79217922198233267034496213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105623896264311022712661617 79217922198233267034496213)
                    ·
                      refine ⟨1856670051521092196121005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79217922198233267034496213 1856670051521092196121005)
                      ·
                        rfl

theorem cell23_3615852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3615852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615852 prefixEnd_3615852 := by exact prefixLift 3615852
  have htrace : WordTrace (prefixWord ++ tailWord_3615852) baseStart_3615852 baseEnd_3615852 := by
    simpa [prefixWord, tailWord_3615852, baseEnd_3615852] using wordTrace_append hprefix tailTrace_3615852
  have hstable : (prefixWord ++ tailWord_3615852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615852).length < 2 ^ (prefixWord ++ tailWord_3615852).sum := by decide
  have hdescent : baseEnd_3615852 < baseStart_3615852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615853 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3615853 : Nat := 118140960795 + 3615853 * 2 ^ 59
def prefixEnd_3615853 : Nat := 4983230072969 + 3 ^ 40 * 3615853 * 2
def baseEnd_3615853 : Nat := 1856670565001746692208501

theorem tailTrace_3615853 : CollatzResearch.WordTrace tailWord_3615853 prefixEnd_3615853 1856670565001746692208501 := by
  unfold tailWord_3615853
  simp only [CollatzResearch.WordTrace]
  refine ⟨131880993369389594372756213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87920662246259729581837475 131880993369389594372756213)
  ·
    refine ⟨12363843128380274472445895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131880993369389594372756213 12363843128380274472445895)
    ·
      refine ⟨18545764692570411708668843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12363843128380274472445895 18545764692570411708668843)
      ·
        refine ⟨27818647038855617563003265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18545764692570411708668843 27818647038855617563003265)
        ·
          refine ⟨20863985279141713172252449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27818647038855617563003265 20863985279141713172252449)
          ·
            refine ⟨15647988959356284879189337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20863985279141713172252449 15647988959356284879189337)
            ·
              refine ⟨11735991719517213659392003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15647988959356284879189337 11735991719517213659392003)
              ·
                refine ⟨17603987579275820489088005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11735991719517213659392003 17603987579275820489088005)
                ·
                  refine ⟨3300747671114216341704001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17603987579275820489088005 3300747671114216341704001)
                  ·
                    refine ⟨2475560753335662256278001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300747671114216341704001 2475560753335662256278001)
                    ·
                      refine ⟨1856670565001746692208501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475560753335662256278001 1856670565001746692208501)
                      ·
                        rfl

theorem cell23_3615853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3615853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615853 prefixEnd_3615853 := by exact prefixLift 3615853
  have htrace : WordTrace (prefixWord ++ tailWord_3615853) baseStart_3615853 baseEnd_3615853 := by
    simpa [prefixWord, tailWord_3615853, baseEnd_3615853] using wordTrace_append hprefix tailTrace_3615853
  have hstable : (prefixWord ++ tailWord_3615853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615853).length < 2 ^ (prefixWord ++ tailWord_3615853).sum := by decide
  have hdescent : baseEnd_3615853 < baseStart_3615853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615869 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_3615869 : Nat := 118140960795 + 3615869 * 2 ^ 59
def prefixEnd_3615869 : Nat := 4983230072969 + 3 ^ 40 * 3615869 * 2
def baseEnd_3615869 : Nat := 1856678780692218629608427

theorem tailTrace_3615869 : CollatzResearch.WordTrace tailWord_3615869 prefixEnd_3615869 1856678780692218629608427 := by
  unfold tailWord_3615869
  simp only [CollatzResearch.WordTrace]
  refine ⟨131881576937331629105338661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87921051291554419403559107 131881576937331629105338661)
  ·
    refine ⟨24727795675749680457250999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131881576937331629105338661 24727795675749680457250999)
    ·
      refine ⟨37091693513624520685876499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727795675749680457250999 37091693513624520685876499)
      ·
        refine ⟨55637540270436781028814749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37091693513624520685876499 55637540270436781028814749)
        ·
          refine ⟨20864077601413792885805531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55637540270436781028814749 20864077601413792885805531)
          ·
            refine ⟨31296116402120689328708297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20864077601413792885805531 31296116402120689328708297)
            ·
              refine ⟨23472087301590516996531223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31296116402120689328708297 23472087301590516996531223)
              ·
                refine ⟨35208130952385775494796835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472087301590516996531223 35208130952385775494796835)
                ·
                  refine ⟨52812196428578663242195253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35208130952385775494796835 52812196428578663242195253)
                  ·
                    refine ⟨4951143415179249678955805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52812196428578663242195253 4951143415179249678955805)
                    ·
                      refine ⟨1856678780692218629608427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951143415179249678955805 1856678780692218629608427)
                      ·
                        rfl

theorem cell23_3615869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_3615869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615869 prefixEnd_3615869 := by exact prefixLift 3615869
  have htrace : WordTrace (prefixWord ++ tailWord_3615869) baseStart_3615869 baseEnd_3615869 := by
    simpa [prefixWord, tailWord_3615869, baseEnd_3615869] using wordTrace_append hprefix tailTrace_3615869
  have hstable : (prefixWord ++ tailWord_3615869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615869).length < 2 ^ (prefixWord ++ tailWord_3615869).sum := by decide
  have hdescent : baseEnd_3615869 < baseStart_3615869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615872 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_3615872 : Nat := 118140960795 + 3615872 * 2 ^ 59
def prefixEnd_3615872 : Nat := 4983230072969 + 3 ^ 40 * 3615872 * 2
def baseEnd_3615872 : Nat := 618893440378060705956971

theorem tailTrace_3615872 : CollatzResearch.WordTrace tailWord_3615872 prefixEnd_3615872 618893440378060705956971 := by
  unfold tailWord_3615872
  simp only [CollatzResearch.WordTrace]
  refine ⟨65940843178160380308848935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87921124237547173745131913 65940843178160380308848935)
  ·
    refine ⟨98911264767240570463273403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65940843178160380308848935 98911264767240570463273403)
    ·
      refine ⟨148366897150860855694910105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98911264767240570463273403 148366897150860855694910105)
      ·
        refine ⟨111275172863145641771182579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148366897150860855694910105 111275172863145641771182579)
        ·
          refine ⟨166912759294718462656773869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111275172863145641771182579 166912759294718462656773869)
          ·
            refine ⟨62592284735519423496290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166912759294718462656773869 62592284735519423496290201)
            ·
              refine ⟨46944213551639567622217651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62592284735519423496290201 46944213551639567622217651)
              ·
                refine ⟨70416320327459351433326477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46944213551639567622217651 70416320327459351433326477)
                ·
                  refine ⟨26406120122797256787497429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70416320327459351433326477 26406120122797256787497429)
                  ·
                    refine ⟨618893440378060705956971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26406120122797256787497429 618893440378060705956971)
                    ·
                      rfl

theorem cell23_3615872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_3615872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615872 prefixEnd_3615872 := by exact prefixLift 3615872
  have htrace : WordTrace (prefixWord ++ tailWord_3615872) baseStart_3615872 baseEnd_3615872 := by
    simpa [prefixWord, tailWord_3615872, baseEnd_3615872] using wordTrace_append hprefix tailTrace_3615872
  have hstable : (prefixWord ++ tailWord_3615872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615872).length < 2 ^ (prefixWord ++ tailWord_3615872).sum := by decide
  have hdescent : baseEnd_3615872 < baseStart_3615872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615940 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3615940 : Nat := 118140960795 + 3615940 * 2 ^ 59
def prefixEnd_3615940 : Nat := 4983230072969 + 3 ^ 40 * 3615940 * 2
def baseEnd_3615940 : Nat := 618905079272895950606867

theorem tailTrace_3615940 : CollatzResearch.WordTrace tailWord_3615940 prefixEnd_3615940 618905079272895950606867 := by
  unfold tailWord_3615940
  simp only [CollatzResearch.WordTrace]
  refine ⟨65942083260037204115586637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87922777680049605487448849 65942083260037204115586637)
  ·
    refine ⟨24728281222513951543344989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65942083260037204115586637 24728281222513951543344989)
    ·
      refine ⟨9273105458442731828754371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24728281222513951543344989 9273105458442731828754371)
      ·
        refine ⟨13909658187664097743131557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273105458442731828754371 13909658187664097743131557)
        ·
          refine ⟨2608060910187018326837167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13909658187664097743131557 2608060910187018326837167)
          ·
            refine ⟨3912091365280527490255751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608060910187018326837167 3912091365280527490255751)
            ·
              refine ⟨5868137047920791235383627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912091365280527490255751 5868137047920791235383627)
              ·
                refine ⟨8802205571881186853075441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868137047920791235383627 8802205571881186853075441)
                ·
                  refine ⟨6601654178910890139806581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802205571881186853075441 6601654178910890139806581)
                  ·
                    refine ⟨618905079272895950606867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6601654178910890139806581 618905079272895950606867)
                    ·
                      rfl

theorem cell23_3615940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3615940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615940 prefixEnd_3615940 := by exact prefixLift 3615940
  have htrace : WordTrace (prefixWord ++ tailWord_3615940) baseStart_3615940 baseEnd_3615940 := by
    simpa [prefixWord, tailWord_3615940, baseEnd_3615940] using wordTrace_append hprefix tailTrace_3615940
  have hstable : (prefixWord ++ tailWord_3615940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615940).length < 2 ^ (prefixWord ++ tailWord_3615940).sum := by decide
  have hdescent : baseEnd_3615940 < baseStart_3615940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615946 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_3615946 : Nat := 118140960795 + 3615946 * 2 ^ 59
def prefixEnd_3615946 : Nat := 4983230072969 + 3 ^ 40 * 3615946 * 2
def baseEnd_3615946 : Nat := 1856718318702614828345573

theorem tailTrace_3615946 : CollatzResearch.WordTrace tailWord_3615946 prefixEnd_3615946 1856718318702614828345573 := by
  unfold tailWord_3615946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32971096339513167813972923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87922923572035114170594461 32971096339513167813972923)
  ·
    refine ⟨49456644509269751720959385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32971096339513167813972923 49456644509269751720959385)
    ·
      refine ⟨37092483381952313790719539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49456644509269751720959385 37092483381952313790719539)
      ·
        refine ⟨55638725072928470686079309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37092483381952313790719539 55638725072928470686079309)
        ·
          refine ⟨20864521902348176507279741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55638725072928470686079309 20864521902348176507279741)
          ·
            refine ⟨7824195713380566190229903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20864521902348176507279741 7824195713380566190229903)
            ·
              refine ⟨11736293570070849285344855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824195713380566190229903 11736293570070849285344855)
              ·
                refine ⟨17604440355106273928017283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736293570070849285344855 17604440355106273928017283)
                ·
                  refine ⟨26406660532659410892025925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17604440355106273928017283 26406660532659410892025925)
                  ·
                    refine ⟨4951248849873639542254861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26406660532659410892025925 4951248849873639542254861)
                    ·
                      refine ⟨1856718318702614828345573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951248849873639542254861 1856718318702614828345573)
                      ·
                        rfl

theorem cell23_3615946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_3615946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615946 prefixEnd_3615946 := by exact prefixLift 3615946
  have htrace : WordTrace (prefixWord ++ tailWord_3615946) baseStart_3615946 baseEnd_3615946 := by
    simpa [prefixWord, tailWord_3615946, baseEnd_3615946] using wordTrace_append hprefix tailTrace_3615946
  have hstable : (prefixWord ++ tailWord_3615946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615946).length < 2 ^ (prefixWord ++ tailWord_3615946).sum := by decide
  have hdescent : baseEnd_3615946 < baseStart_3615946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615969 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3615969 : Nat := 118140960795 + 3615969 * 2 ^ 59
def prefixEnd_3615969 : Nat := 4983230072969 + 3 ^ 40 * 3615969 * 2
def baseEnd_3615969 : Nat := 1856730128757668238357967

theorem tailTrace_3615969 : CollatzResearch.WordTrace tailWord_3615969 prefixEnd_3615969 1856730128757668238357967 := by
  unfold tailWord_3615969
  simp only [CollatzResearch.WordTrace]
  refine ⟨131885224236969346183978961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87923482824646230789319307 131885224236969346183978961)
  ·
    refine ⟨98913918177727009637984221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131885224236969346183978961 98913918177727009637984221)
    ·
      refine ⟨37092719316647628614244083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98913918177727009637984221 37092719316647628614244083)
      ·
        refine ⟨55639078974971442921366125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37092719316647628614244083 55639078974971442921366125)
        ·
          refine ⟨20864654615614291095512297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55639078974971442921366125 20864654615614291095512297)
          ·
            refine ⟨15648490961710718321634223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20864654615614291095512297 15648490961710718321634223)
            ·
              refine ⟨23472736442566077482451335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648490961710718321634223 23472736442566077482451335)
              ·
                refine ⟨35209104663849116223677003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472736442566077482451335 35209104663849116223677003)
                ·
                  refine ⟨52813656995773674335515505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35209104663849116223677003 52813656995773674335515505)
                  ·
                    refine ⟨39610242746830255751636629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52813656995773674335515505 39610242746830255751636629)
                    ·
                      refine ⟨1856730128757668238357967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39610242746830255751636629 1856730128757668238357967)
                      ·
                        rfl

theorem cell23_3615969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3615969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615969 prefixEnd_3615969 := by exact prefixLift 3615969
  have htrace : WordTrace (prefixWord ++ tailWord_3615969) baseStart_3615969 baseEnd_3615969 := by
    simpa [prefixWord, tailWord_3615969, baseEnd_3615969] using wordTrace_append hprefix tailTrace_3615969
  have hstable : (prefixWord ++ tailWord_3615969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615969).length < 2 ^ (prefixWord ++ tailWord_3615969).sum := by decide
  have hdescent : baseEnd_3615969 < baseStart_3615969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3615983 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 6]
def baseStart_3615983 : Nat := 118140960795 + 3615983 * 2 ^ 59
def prefixEnd_3615983 : Nat := 4983230072969 + 3 ^ 40 * 3615983 * 2
def baseEnd_3615983 : Nat := 206304146387425687064767

theorem tailTrace_3615983 : CollatzResearch.WordTrace tailWord_3615983 prefixEnd_3615983 206304146387425687064767 := by
  unfold tailWord_3615983
  simp only [CollatzResearch.WordTrace]
  refine ⟨131885734858918626574988603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87923823239279084383325735 131885734858918626574988603)
  ·
    refine ⟨197828602288377939862482905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131885734858918626574988603 197828602288377939862482905)
    ·
      refine ⟨148371451716283454896862179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197828602288377939862482905 148371451716283454896862179)
      ·
        refine ⟨222557177574425182345293269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148371451716283454896862179 222557177574425182345293269)
        ·
          refine ⟨5216183849400590211217811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 222557177574425182345293269 5216183849400590211217811)
          ·
            refine ⟨7824275774100885316826717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216183849400590211217811 7824275774100885316826717)
            ·
              refine ⟨2934103415287831993810019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7824275774100885316826717 2934103415287831993810019)
              ·
                refine ⟨4401155122931747990715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934103415287831993810019 4401155122931747990715029)
                ·
                  refine ⟨206304146387425687064767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4401155122931747990715029 206304146387425687064767)
                  ·
                    rfl

theorem cell23_3615983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 6].length) (baseStart_3615983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3615983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3615983 prefixEnd_3615983 := by exact prefixLift 3615983
  have htrace : WordTrace (prefixWord ++ tailWord_3615983) baseStart_3615983 baseEnd_3615983 := by
    simpa [prefixWord, tailWord_3615983, baseEnd_3615983] using wordTrace_append hprefix tailTrace_3615983
  have hstable : (prefixWord ++ tailWord_3615983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3615983).length < 2 ^ (prefixWord ++ tailWord_3615983).sum := by decide
  have hdescent : baseEnd_3615983 < baseStart_3615983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3615983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616009 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_3616009 : Nat := 118140960795 + 3616009 * 2 ^ 59
def prefixEnd_3616009 : Nat := 4983230072969 + 3 ^ 40 * 3616009 * 2
def baseEnd_3616009 : Nat := 618916889327949360619261

theorem tailTrace_3616009 : CollatzResearch.WordTrace tailWord_3616009 prefixEnd_3616009 618916889327949360619261 := by
  unfold tailWord_3616009
  simp only [CollatzResearch.WordTrace]
  refine ⟨131886683156824433015435081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87924455437882955343623387 131886683156824433015435081)
  ·
    refine ⟨98915012367618324761576311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131886683156824433015435081 98915012367618324761576311)
    ·
      refine ⟨148372518551427487142364467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98915012367618324761576311 148372518551427487142364467)
      ·
        refine ⟨222558777827141230713546701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148372518551427487142364467 222558777827141230713546701)
        ·
          refine ⟨83459541685177961517580013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222558777827141230713546701 83459541685177961517580013)
          ·
            refine ⟨31297328131941735569092505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83459541685177961517580013 31297328131941735569092505)
            ·
              refine ⟨23472996098956301676819379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31297328131941735569092505 23472996098956301676819379)
              ·
                refine ⟨35209494148434452515229069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23472996098956301676819379 35209494148434452515229069)
                ·
                  refine ⟨13203560305662919693210901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35209494148434452515229069 13203560305662919693210901)
                  ·
                    refine ⟨618916889327949360619261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13203560305662919693210901 618916889327949360619261)
                    ·
                      rfl

theorem cell23_3616009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_3616009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616009 prefixEnd_3616009 := by exact prefixLift 3616009
  have htrace : WordTrace (prefixWord ++ tailWord_3616009) baseStart_3616009 baseEnd_3616009 := by
    simpa [prefixWord, tailWord_3616009, baseEnd_3616009] using wordTrace_append hprefix tailTrace_3616009
  have hstable : (prefixWord ++ tailWord_3616009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616009).length < 2 ^ (prefixWord ++ tailWord_3616009).sum := by decide
  have hdescent : baseEnd_3616009 < baseStart_3616009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616036 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3616036 : Nat := 118140960795 + 3616036 * 2 ^ 59
def prefixEnd_3616036 : Nat := 4983230072969 + 3 ^ 40 * 3616036 * 2
def baseEnd_3616036 : Nat := 1856764531961519476220159

theorem tailTrace_3616036 : CollatzResearch.WordTrace tailWord_3616036 prefixEnd_3616036 1856764531961519476220159 := by
  unfold tailWord_3616036
  simp only [CollatzResearch.WordTrace]
  refine ⟨65943833963863308313333981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87925111951817744417778641 65943833963863308313333981)
  ·
    refine ⟨24728937736448740617500243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65943833963863308313333981 24728937736448740617500243)
    ·
      refine ⟨37093406604673110926250365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24728937736448740617500243 37093406604673110926250365)
      ·
        refine ⟨13910027476752416597343887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37093406604673110926250365 13910027476752416597343887)
        ·
          refine ⟨20865041215128624896015831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910027476752416597343887 20865041215128624896015831)
          ·
            refine ⟨31297561822692937344023747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20865041215128624896015831 31297561822692937344023747)
            ·
              refine ⟨46946342734039406016035621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31297561822692937344023747 46946342734039406016035621)
              ·
                refine ⟨8802439262632388628006679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46946342734039406016035621 8802439262632388628006679)
                ·
                  refine ⟨13203658893948582942010019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802439262632388628006679 13203658893948582942010019)
                  ·
                    refine ⟨19805488340922874413015029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13203658893948582942010019 19805488340922874413015029)
                    ·
                      refine ⟨1856764531961519476220159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19805488340922874413015029 1856764531961519476220159)
                      ·
                        rfl

theorem cell23_3616036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3616036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616036 prefixEnd_3616036 := by exact prefixLift 3616036
  have htrace : WordTrace (prefixWord ++ tailWord_3616036) baseStart_3616036 baseEnd_3616036 := by
    simpa [prefixWord, tailWord_3616036, baseEnd_3616036] using wordTrace_append hprefix tailTrace_3616036
  have hstable : (prefixWord ++ tailWord_3616036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616036).length < 2 ^ (prefixWord ++ tailWord_3616036).sum := by decide
  have hdescent : baseEnd_3616036 < baseStart_3616036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616050 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3616050 : Nat := 118140960795 + 3616050 * 2 ^ 59
def prefixEnd_3616050 : Nat := 4983230072969 + 3 ^ 40 * 3616050 * 2
def baseEnd_3616050 : Nat := 1856771720690682421445095

theorem tailTrace_3616050 : CollatzResearch.WordTrace tailWord_3616050 prefixEnd_3616050 1856771720690682421445095 := by
  unfold tailWord_3616050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32972044637418974254419401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87925452366450598011785069 32972044637418974254419401)
  ·
    refine ⟨24729033478064230690814551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32972044637418974254419401 24729033478064230690814551)
    ·
      refine ⟨37093550217096346036221827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24729033478064230690814551 37093550217096346036221827)
      ·
        refine ⟨55640325325644519054332741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37093550217096346036221827 55640325325644519054332741)
        ·
          refine ⟨10432560998558347322687389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55640325325644519054332741 10432560998558347322687389)
          ·
            refine ⟨3912210374459380246007771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10432560998558347322687389 3912210374459380246007771)
            ·
              refine ⟨5868315561689070369011657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912210374459380246007771 5868315561689070369011657)
              ·
                refine ⟨4401236671266802776758743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868315561689070369011657 4401236671266802776758743)
                ·
                  refine ⟨6601855006900204165138115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401236671266802776758743 6601855006900204165138115)
                  ·
                    refine ⟨9902782510350306247707173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6601855006900204165138115 9902782510350306247707173)
                    ·
                      refine ⟨1856771720690682421445095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9902782510350306247707173 1856771720690682421445095)
                      ·
                        rfl

theorem cell23_3616050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3616050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616050 prefixEnd_3616050 := by exact prefixLift 3616050
  have htrace : WordTrace (prefixWord ++ tailWord_3616050) baseStart_3616050 baseEnd_3616050 := by
    simpa [prefixWord, tailWord_3616050, baseEnd_3616050] using wordTrace_append hprefix tailTrace_3616050
  have hstable : (prefixWord ++ tailWord_3616050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616050).length < 2 ^ (prefixWord ++ tailWord_3616050).sum := by decide
  have hdescent : baseEnd_3616050 < baseStart_3616050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616053 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3616053 : Nat := 118140960795 + 3616053 * 2 ^ 59
def prefixEnd_3616053 : Nat := 4983230072969 + 3 ^ 40 * 3616053 * 2
def baseEnd_3616053 : Nat := 1856773261132645909707581

theorem tailTrace_3616053 : CollatzResearch.WordTrace tailWord_3616053 prefixEnd_3616053 1856773261132645909707581 := by
  unfold tailWord_3616053
  simp only [CollatzResearch.WordTrace]
  refine ⟨131888287968665028530036813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87925525312443352353357875 131888287968665028530036813)
  ·
    refine ⟨49458107988249385698763805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131888287968665028530036813 49458107988249385698763805)
    ·
      refine ⟨18546790495593519637036427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49458107988249385698763805 18546790495593519637036427)
      ·
        refine ⟨27820185743390279455554641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18546790495593519637036427 27820185743390279455554641)
        ·
          refine ⟨20865139307542709591665981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27820185743390279455554641 20865139307542709591665981)
          ·
            refine ⟨7824427240328516096874743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20865139307542709591665981 7824427240328516096874743)
            ·
              refine ⟨11736640860492774145312115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824427240328516096874743 11736640860492774145312115)
              ·
                refine ⟨17604961290739161217968173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736640860492774145312115 17604961290739161217968173)
                ·
                  refine ⟨6601860484027185456738065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17604961290739161217968173 6601860484027185456738065)
                  ·
                    refine ⟨4951395363020389092553549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601860484027185456738065 4951395363020389092553549)
                    ·
                      refine ⟨1856773261132645909707581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951395363020389092553549 1856773261132645909707581)
                      ·
                        rfl

theorem cell23_3616053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3616053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616053 prefixEnd_3616053 := by exact prefixLift 3616053
  have htrace : WordTrace (prefixWord ++ tailWord_3616053) baseStart_3616053 baseEnd_3616053 := by
    simpa [prefixWord, tailWord_3616053, baseEnd_3616053] using wordTrace_append hprefix tailTrace_3616053
  have hstable : (prefixWord ++ tailWord_3616053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616053).length < 2 ^ (prefixWord ++ tailWord_3616053).sum := by decide
  have hdescent : baseEnd_3616053 < baseStart_3616053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616054 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3616054 : Nat := 118140960795 + 3616054 * 2 ^ 59
def prefixEnd_3616054 : Nat := 4983230072969 + 3 ^ 40 * 3616054 * 2
def baseEnd_3616054 : Nat := 1856773774613300405795077

theorem tailTrace_3616054 : CollatzResearch.WordTrace tailWord_3616054 prefixEnd_3616054 1856773774613300405795077 := by
  unfold tailWord_3616054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243020277603837856301451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87925549627774270467215477 8243020277603837856301451)
  ·
    refine ⟨12364530416405756784452177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8243020277603837856301451 12364530416405756784452177)
    ·
      refine ⟨9273397812304317588339133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12364530416405756784452177 9273397812304317588339133)
      ·
        refine ⟨3477524179614119095627175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9273397812304317588339133 3477524179614119095627175)
        ·
          refine ⟨5216286269421178643440763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477524179614119095627175 5216286269421178643440763)
          ·
            refine ⟨7824429404131767965161145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216286269421178643440763 7824429404131767965161145)
            ·
              refine ⟨5868322053098825973870859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824429404131767965161145 5868322053098825973870859)
              ·
                refine ⟨8802483079648238960806289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868322053098825973870859 8802483079648238960806289)
                ·
                  refine ⟨6601862309736179220604717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802483079648238960806289 6601862309736179220604717)
                  ·
                    refine ⟨2475698366151067207726769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6601862309736179220604717 2475698366151067207726769)
                    ·
                      refine ⟨1856773774613300405795077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475698366151067207726769 1856773774613300405795077)
                      ·
                        rfl

theorem cell23_3616054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3616054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616054 prefixEnd_3616054 := by exact prefixLift 3616054
  have htrace : WordTrace (prefixWord ++ tailWord_3616054) baseStart_3616054 baseEnd_3616054 := by
    simpa [prefixWord, tailWord_3616054, baseEnd_3616054] using wordTrace_append hprefix tailTrace_3616054
  have hstable : (prefixWord ++ tailWord_3616054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616054).length < 2 ^ (prefixWord ++ tailWord_3616054).sum := by decide
  have hdescent : baseEnd_3616054 < baseStart_3616054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616069 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3616069 : Nat := 118140960795 + 3616069 * 2 ^ 59
def prefixEnd_3616069 : Nat := 4983230072969 + 3 ^ 40 * 3616069 * 2
def baseEnd_3616069 : Nat := 618927158941039282369169

theorem tailTrace_3616069 : CollatzResearch.WordTrace tailWord_3616069 prefixEnd_3616069 618927158941039282369169 := by
  unfold tailWord_3616069
  simp only [CollatzResearch.WordTrace]
  refine ⟨131888871536607063262619261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87925914357738042175079507 131888871536607063262619261)
  ·
    refine ⟨49458326826227648723482223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131888871536607063262619261 49458326826227648723482223)
    ·
      refine ⟨74187490239341473085223335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49458326826227648723482223 74187490239341473085223335)
      ·
        refine ⟨111281235359012209627835003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74187490239341473085223335 111281235359012209627835003)
        ·
          refine ⟨166921853038518314441752505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111281235359012209627835003 166921853038518314441752505)
          ·
            refine ⟨125191389778888735831314379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166921853038518314441752505 125191389778888735831314379)
            ·
              refine ⟨187787084668333103746971569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125191389778888735831314379 187787084668333103746971569)
              ·
                refine ⟨140840313501249827810228677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187787084668333103746971569 140840313501249827810228677)
                ·
                  refine ⟨26407558781484342714417877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140840313501249827810228677 26407558781484342714417877)
                  ·
                    refine ⟨618927158941039282369169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26407558781484342714417877 618927158941039282369169)
                    ·
                      rfl

theorem cell23_3616069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3616069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616069 prefixEnd_3616069 := by exact prefixLift 3616069
  have htrace : WordTrace (prefixWord ++ tailWord_3616069) baseStart_3616069 baseEnd_3616069 := by
    simpa [prefixWord, tailWord_3616069, baseEnd_3616069] using wordTrace_append hprefix tailTrace_3616069
  have hstable : (prefixWord ++ tailWord_3616069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616069).length < 2 ^ (prefixWord ++ tailWord_3616069).sum := by decide
  have hdescent : baseEnd_3616069 < baseStart_3616069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616079 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_3616079 : Nat := 118140960795 + 3616079 * 2 ^ 59
def prefixEnd_3616079 : Nat := 4983230072969 + 3 ^ 40 * 3616079 * 2
def baseEnd_3616079 : Nat := 1856786611629662807982461

theorem tailTrace_3616079 : CollatzResearch.WordTrace tailWord_3616079 prefixEnd_3616079 1856786611629662807982461 := by
  unfold tailWord_3616079
  simp only [CollatzResearch.WordTrace]
  refine ⟨131889236266570834970483291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87926157511047223313655527 131889236266570834970483291)
  ·
    refine ⟨197833854399856252455724937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131889236266570834970483291 197833854399856252455724937)
    ·
      refine ⟨148375390799892189341793703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197833854399856252455724937 148375390799892189341793703)
      ·
        refine ⟨222563086199838284012690555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148375390799892189341793703 222563086199838284012690555)
        ·
          refine ⟨333844629299757426019035833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222563086199838284012690555 333844629299757426019035833)
          ·
            refine ⟨250383471974818069514276875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333844629299757426019035833 250383471974818069514276875)
            ·
              refine ⟨375575207962227104271415313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250383471974818069514276875 375575207962227104271415313)
              ·
                refine ⟨281681405971670328203561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375575207962227104271415313 281681405971670328203561485)
                ·
                  refine ⟨105630527239376373076335557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281681405971670328203561485 105630527239376373076335557)
                  ·
                    refine ⟨19805723857383069951812917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105630527239376373076335557 19805723857383069951812917)
                    ·
                      refine ⟨1856786611629662807982461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19805723857383069951812917 1856786611629662807982461)
                      ·
                        rfl

theorem cell23_3616079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_3616079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616079 prefixEnd_3616079 := by exact prefixLift 3616079
  have htrace : WordTrace (prefixWord ++ tailWord_3616079) baseStart_3616079 baseEnd_3616079 := by
    simpa [prefixWord, tailWord_3616079, baseEnd_3616079] using wordTrace_append hprefix tailTrace_3616079
  have hstable : (prefixWord ++ tailWord_3616079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616079).length < 2 ^ (prefixWord ++ tailWord_3616079).sum := by decide
  have hdescent : baseEnd_3616079 < baseStart_3616079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616100 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_3616100 : Nat := 118140960795 + 3616100 * 2 ^ 59
def prefixEnd_3616100 : Nat := 4983230072969 + 3 ^ 40 * 3616100 * 2
def baseEnd_3616100 : Nat := 1856797394723407225819865

theorem tailTrace_3616100 : CollatzResearch.WordTrace tailWord_3616100 prefixEnd_3616100 1856797394723407225819865 := by
  unfold tailWord_3616100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65945001099747377778498877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87926668132996503704665169 65945001099747377778498877)
  ·
    refine ⟨24729375412405266666937079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65945001099747377778498877 24729375412405266666937079)
    ·
      refine ⟨37094063118607900000405619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24729375412405266666937079 37094063118607900000405619)
      ·
        refine ⟨55641094677911850000608429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37094063118607900000405619 55641094677911850000608429)
        ·
          refine ⟨20865410504216943750228161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55641094677911850000608429 20865410504216943750228161)
          ·
            refine ⟨15649057878162707812671121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20865410504216943750228161 15649057878162707812671121)
            ·
              refine ⟨11736793408622030859503341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15649057878162707812671121 11736793408622030859503341)
              ·
                refine ⟨4401297528233261572313753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11736793408622030859503341 4401297528233261572313753)
                ·
                  refine ⟨3300973146174946179235315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4401297528233261572313753 3300973146174946179235315)
                  ·
                    refine ⟨4951459719262419268852973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300973146174946179235315 4951459719262419268852973)
                    ·
                      refine ⟨1856797394723407225819865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951459719262419268852973 1856797394723407225819865)
                      ·
                        rfl

theorem cell23_3616100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_3616100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616100 prefixEnd_3616100 := by exact prefixLift 3616100
  have htrace : WordTrace (prefixWord ++ tailWord_3616100) baseStart_3616100 baseEnd_3616100 := by
    simpa [prefixWord, tailWord_3616100, baseEnd_3616100] using wordTrace_append hprefix tailTrace_3616100
  have hstable : (prefixWord ++ tailWord_3616100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616100).length < 2 ^ (prefixWord ++ tailWord_3616100).sum := by decide
  have hdescent : baseEnd_3616100 < baseStart_3616100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616123 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 4, 2]
def baseStart_3616123 : Nat := 118140960795 + 3616123 * 2 ^ 59
def prefixEnd_3616123 : Nat := 4983230072969 + 3 ^ 40 * 3616123 * 2
def baseEnd_3616123 : Nat := 1856809204778460635832259

theorem tailTrace_3616123 : CollatzResearch.WordTrace tailWord_3616123 prefixEnd_3616123 1856809204778460635832259 := by
  unfold tailWord_3616123
  simp only [CollatzResearch.WordTrace]
  refine ⟨131890841078411430485085023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87927227385607620323390015 131890841078411430485085023)
  ·
    refine ⟨197836261617617145727627535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131890841078411430485085023 197836261617617145727627535)
    ·
      refine ⟨296754392426425718591441303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197836261617617145727627535 296754392426425718591441303)
      ·
        refine ⟨445131588639638577887161955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296754392426425718591441303 445131588639638577887161955)
        ·
          refine ⟨667697382959457866830742933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445131588639638577887161955 667697382959457866830742933)
          ·
            refine ⟨31298314826224587507691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 667697382959457866830742933 31298314826224587507691075)
            ·
              refine ⟨46947472239336881261536613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31298314826224587507691075 46947472239336881261536613)
              ·
                refine ⟨8802651044875665236538115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46947472239336881261536613 8802651044875665236538115)
                ·
                  refine ⟨13203976567313497854807173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802651044875665236538115 13203976567313497854807173)
                  ·
                    refine ⟨2475745606371280847776345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13203976567313497854807173 2475745606371280847776345)
                    ·
                      refine ⟨1856809204778460635832259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475745606371280847776345 1856809204778460635832259)
                      ·
                        rfl

theorem cell23_3616123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4, 2].length) (baseStart_3616123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616123 prefixEnd_3616123 := by exact prefixLift 3616123
  have htrace : WordTrace (prefixWord ++ tailWord_3616123) baseStart_3616123 baseEnd_3616123 := by
    simpa [prefixWord, tailWord_3616123, baseEnd_3616123] using wordTrace_append hprefix tailTrace_3616123
  have hstable : (prefixWord ++ tailWord_3616123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616123).length < 2 ^ (prefixWord ++ tailWord_3616123).sum := by decide
  have hdescent : baseEnd_3616123 < baseStart_3616123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616140 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_3616140 : Nat := 118140960795 + 3616140 * 2 ^ 59
def prefixEnd_3616140 : Nat := 4983230072969 + 3 ^ 40 * 3616140 * 2
def baseEnd_3616140 : Nat := 1856817933949587069319681

theorem tailTrace_3616140 : CollatzResearch.WordTrace tailWord_3616140 prefixEnd_3616140 1856817933949587069319681 := by
  unfold tailWord_3616140
  simp only [CollatzResearch.WordTrace]
  refine ⟨65945730559674921194226937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87927640746233228258969249 65945730559674921194226937)
  ·
    refine ⟨49459297919756190895670203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65945730559674921194226937 49459297919756190895670203)
    ·
      refine ⟨74188946879634286343505305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49459297919756190895670203 74188946879634286343505305)
      ·
        refine ⟨55641710159725714757628979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74188946879634286343505305 55641710159725714757628979)
        ·
          refine ⟨83462565239588572136443469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55641710159725714757628979 83462565239588572136443469)
          ·
            refine ⟨31298461964845714551166301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83462565239588572136443469 31298461964845714551166301)
            ·
              refine ⟨11736923236817142956687363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31298461964845714551166301 11736923236817142956687363)
              ·
                refine ⟨17605384855225714435031045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736923236817142956687363 17605384855225714435031045)
                ·
                  refine ⟨3301009660354821456568321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17605384855225714435031045 3301009660354821456568321)
                  ·
                    refine ⟨2475757245266116092426241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3301009660354821456568321 2475757245266116092426241)
                    ·
                      refine ⟨1856817933949587069319681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475757245266116092426241 1856817933949587069319681)
                      ·
                        rfl

theorem cell23_3616140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_3616140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616140 prefixEnd_3616140 := by exact prefixLift 3616140
  have htrace : WordTrace (prefixWord ++ tailWord_3616140) baseStart_3616140 baseEnd_3616140 := by
    simpa [prefixWord, tailWord_3616140, baseEnd_3616140] using wordTrace_append hprefix tailTrace_3616140
  have hstable : (prefixWord ++ tailWord_3616140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616140).length < 2 ^ (prefixWord ++ tailWord_3616140).sum := by decide
  have hdescent : baseEnd_3616140 < baseStart_3616140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616157 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_3616157 : Nat := 118140960795 + 3616157 * 2 ^ 59
def prefixEnd_3616157 : Nat := 4983230072969 + 3 ^ 40 * 3616157 * 2
def baseEnd_3616157 : Nat := 1856826663120713502807103

theorem tailTrace_3616157 : CollatzResearch.WordTrace tailWord_3616157 prefixEnd_3616157 1856826663120713502807103 := by
  unfold tailWord_3616157
  simp only [CollatzResearch.WordTrace]
  refine ⟨131892081160288254291822725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87928054106858836194548483 131892081160288254291822725)
  ·
    refine ⟨24729765217554047679716761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131892081160288254291822725 24729765217554047679716761)
    ·
      refine ⟨18547323913165535759787571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24729765217554047679716761 18547323913165535759787571)
      ·
        refine ⟨27820985869748303639681357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18547323913165535759787571 27820985869748303639681357)
        ·
          refine ⟨10432869701155613864880509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27820985869748303639681357 10432869701155613864880509)
          ·
            refine ⟨3912326137933355199330191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10432869701155613864880509 3912326137933355199330191)
            ·
              refine ⟨5868489206900032798995287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912326137933355199330191 5868489206900032798995287)
              ·
                refine ⟨8802733810350049198492931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868489206900032798995287 8802733810350049198492931)
                ·
                  refine ⟨13204100715525073797739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8802733810350049198492931 13204100715525073797739397)
                  ·
                    refine ⟨2475768884160951337076137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13204100715525073797739397 2475768884160951337076137)
                    ·
                      refine ⟨1856826663120713502807103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475768884160951337076137 1856826663120713502807103)
                      ·
                        rfl

theorem cell23_3616157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_3616157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616157 prefixEnd_3616157 := by exact prefixLift 3616157
  have htrace : WordTrace (prefixWord ++ tailWord_3616157) baseStart_3616157 baseEnd_3616157 := by
    simpa [prefixWord, tailWord_3616157, baseEnd_3616157] using wordTrace_append hprefix tailTrace_3616157
  have hstable : (prefixWord ++ tailWord_3616157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616157).length < 2 ^ (prefixWord ++ tailWord_3616157).sum := by decide
  have hdescent : baseEnd_3616157 < baseStart_3616157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616213 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3616213 : Nat := 118140960795 + 3616213 * 2 ^ 59
def prefixEnd_3616213 : Nat := 4983230072969 + 3 ^ 40 * 3616213 * 2
def baseEnd_3616213 : Nat := 1856855418037365283706845

theorem tailTrace_3616213 : CollatzResearch.WordTrace tailWord_3616213 prefixEnd_3616213 1856855418037365283706845 := by
  unfold tailWord_3616213
  simp only [CollatzResearch.WordTrace]
  refine ⟨131894123648085375855861293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87929415765390250570574195 131894123648085375855861293)
  ·
    refine ⟨49460296368032015945947985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131894123648085375855861293 49460296368032015945947985)
    ·
      refine ⟨37095222276024011959460989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49460296368032015945947985 37095222276024011959460989)
      ·
        refine ⟨13910708353509004484797871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37095222276024011959460989 13910708353509004484797871)
        ·
          refine ⟨20866062530263506727196807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910708353509004484797871 20866062530263506727196807)
          ·
            refine ⟨31299093795395260090795211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20866062530263506727196807 31299093795395260090795211)
            ·
              refine ⟨46948640693092890136192817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31299093795395260090795211 46948640693092890136192817)
              ·
                refine ⟨35211480519819667602144613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46948640693092890136192817 35211480519819667602144613)
                ·
                  refine ⟨6602152597466187675402115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35211480519819667602144613 6602152597466187675402115)
                  ·
                    refine ⟨9903228896199281513103173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6602152597466187675402115 9903228896199281513103173)
                    ·
                      refine ⟨1856855418037365283706845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9903228896199281513103173 1856855418037365283706845)
                      ·
                        rfl

theorem cell23_3616213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3616213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616213 prefixEnd_3616213 := by exact prefixLift 3616213
  have htrace : WordTrace (prefixWord ++ tailWord_3616213) baseStart_3616213 baseEnd_3616213 := by
    simpa [prefixWord, tailWord_3616213, baseEnd_3616213] using wordTrace_append hprefix tailTrace_3616213
  have hstable : (prefixWord ++ tailWord_3616213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616213).length < 2 ^ (prefixWord ++ tailWord_3616213).sum := by decide
  have hdescent : baseEnd_3616213 < baseStart_3616213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616223 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 5, 4]
def baseStart_3616223 : Nat := 118140960795 + 3616223 * 2 ^ 59
def prefixEnd_3616223 : Nat := 4983230072969 + 3 ^ 40 * 3616223 * 2
def baseEnd_3616223 : Nat := 618953517614636748193933

theorem tailTrace_3616223 : CollatzResearch.WordTrace tailWord_3616223 prefixEnd_3616223 618953517614636748193933 := by
  unfold tailWord_3616223
  simp only [CollatzResearch.WordTrace]
  refine ⟨131894488378049147563725323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87929658918699431709150215 131894488378049147563725323)
  ·
    refine ⟨197841732567073721345587985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131894488378049147563725323 197841732567073721345587985)
    ·
      refine ⟨148381299425305291009190989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197841732567073721345587985 148381299425305291009190989)
      ·
        refine ⟨55642987284489484128446621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148381299425305291009190989 55642987284489484128446621)
        ·
          refine ⟨20866120231683556548167483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55642987284489484128446621 20866120231683556548167483)
          ·
            refine ⟨31299180347525334822251225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20866120231683556548167483 31299180347525334822251225)
            ·
              refine ⟨23474385260644001116688419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31299180347525334822251225 23474385260644001116688419)
              ·
                refine ⟨35211577890966001675032629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23474385260644001116688419 35211577890966001675032629)
                ·
                  refine ⟨3301085427278062657034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35211577890966001675032629 3301085427278062657034309)
                  ·
                    refine ⟨618953517614636748193933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301085427278062657034309 618953517614636748193933)
                    ·
                      rfl

theorem cell23_3616223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_3616223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616223 prefixEnd_3616223 := by exact prefixLift 3616223
  have htrace : WordTrace (prefixWord ++ tailWord_3616223) baseStart_3616223 baseEnd_3616223 := by
    simpa [prefixWord, tailWord_3616223, baseEnd_3616223] using wordTrace_append hprefix tailTrace_3616223
  have hstable : (prefixWord ++ tailWord_3616223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616223).length < 2 ^ (prefixWord ++ tailWord_3616223).sum := by decide
  have hdescent : baseEnd_3616223 < baseStart_3616223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616236 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 8]
def baseStart_3616236 : Nat := 118140960795 + 3616236 * 2 ^ 59
def prefixEnd_3616236 : Nat := 4983230072969 + 3 ^ 40 * 3616236 * 2
def baseEnd_3616236 : Nat := 206318580899157632635471

theorem tailTrace_3616236 : CollatzResearch.WordTrace tailWord_3616236 prefixEnd_3616236 206318580899157632635471 := by
  unfold tailWord_3616236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65947481263501025391974281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87929975018001367189299041 65947481263501025391974281)
  ·
    refine ⟨49460610947625769043980711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65947481263501025391974281 49460610947625769043980711)
    ·
      refine ⟨74190916421438653565971067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49460610947625769043980711 74190916421438653565971067)
      ·
        refine ⟨111286374632157980348956601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74190916421438653565971067 111286374632157980348956601)
        ·
          refine ⟨83464780974118485261717451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111286374632157980348956601 83464780974118485261717451)
          ·
            refine ⟨125197171461177727892576177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83464780974118485261717451 125197171461177727892576177)
            ·
              refine ⟨93897878595883295919432133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125197171461177727892576177 93897878595883295919432133)
              ·
                refine ⟨17605852236728117984893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93897878595883295919432133 17605852236728117984893525)
                ·
                  refine ⟨206318580899157632635471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17605852236728117984893525 206318580899157632635471)
                  ·
                    rfl

theorem cell23_3616236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_3616236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616236 prefixEnd_3616236 := by exact prefixLift 3616236
  have htrace : WordTrace (prefixWord ++ tailWord_3616236) baseStart_3616236 baseEnd_3616236 := by
    simpa [prefixWord, tailWord_3616236, baseEnd_3616236] using wordTrace_append hprefix tailTrace_3616236
  have hstable : (prefixWord ++ tailWord_3616236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616236).length < 2 ^ (prefixWord ++ tailWord_3616236).sum := by decide
  have hdescent : baseEnd_3616236 < baseStart_3616236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616253 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 6]
def baseStart_3616253 : Nat := 118140960795 + 3616253 * 2 ^ 59
def prefixEnd_3616253 : Nat := 4983230072969 + 3 ^ 40 * 3616253 * 2
def baseEnd_3616253 : Nat := 206319550807060569689629

theorem tailTrace_3616253 : CollatzResearch.WordTrace tailWord_3616253 prefixEnd_3616253 206319550807060569689629 := by
  unfold tailWord_3616253
  simp only [CollatzResearch.WordTrace]
  refine ⟨131895582567940462687317413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87930388378626975124878275 131895582567940462687317413)
  ·
    refine ⟨24730421731488836753872015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131895582567940462687317413 24730421731488836753872015)
    ·
      refine ⟨37095632597233255130808023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24730421731488836753872015 37095632597233255130808023)
      ·
        refine ⟨55643448895849882696212035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37095632597233255130808023 55643448895849882696212035)
        ·
          refine ⟨83465173343774824044318053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55643448895849882696212035 83465173343774824044318053)
          ·
            refine ⟨15649720001957779508309635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83465173343774824044318053 15649720001957779508309635)
            ·
              refine ⟨23474580002936669262464453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15649720001957779508309635 23474580002936669262464453)
              ·
                refine ⟨4401483750550625486712085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23474580002936669262464453 4401483750550625486712085)
                ·
                  refine ⟨206319550807060569689629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4401483750550625486712085 206319550807060569689629)
                  ·
                    rfl

theorem cell23_3616253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_3616253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616253 prefixEnd_3616253 := by exact prefixLift 3616253
  have htrace : WordTrace (prefixWord ++ tailWord_3616253) baseStart_3616253 baseEnd_3616253 := by
    simpa [prefixWord, tailWord_3616253, baseEnd_3616253] using wordTrace_append hprefix tailTrace_3616253
  have hstable : (prefixWord ++ tailWord_3616253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616253).length < 2 ^ (prefixWord ++ tailWord_3616253).sum := by decide
  have hdescent : baseEnd_3616253 < baseStart_3616253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616337 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_3616337 : Nat := 118140960795 + 3616337 * 2 ^ 59
def prefixEnd_3616337 : Nat := 4983230072969 + 3 ^ 40 * 3616337 * 2
def baseEnd_3616337 : Nat := 1856919089638522798556275

theorem tailTrace_3616337 : CollatzResearch.WordTrace tailWord_3616337 prefixEnd_3616337 1856919089638522798556275 := by
  unfold tailWord_3616337
  simp only [CollatzResearch.WordTrace]
  refine ⟨131898646299636145033375265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87932430866424096688916843 131898646299636145033375265)
  ·
    refine ⟨98923984724727108775031449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131898646299636145033375265 98923984724727108775031449)
    ·
      refine ⟨74192988543545331581273587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98923984724727108775031449 74192988543545331581273587)
      ·
        refine ⟨111289482815317997371910381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74192988543545331581273587 111289482815317997371910381)
        ·
          refine ⟨41733556055744249014466393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111289482815317997371910381 41733556055744249014466393)
          ·
            refine ⟨31300167041808186760849795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41733556055744249014466393 31300167041808186760849795)
            ·
              refine ⟨46950250562712280141274693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31300167041808186760849795 46950250562712280141274693)
              ·
                refine ⟨8803171980508552526489005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46950250562712280141274693 8803171980508552526489005)
                ·
                  refine ⟨3301189492690707197433377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8803171980508552526489005 3301189492690707197433377)
                  ·
                    refine ⟨2475892119518030398075033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3301189492690707197433377 2475892119518030398075033)
                    ·
                      refine ⟨1856919089638522798556275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475892119518030398075033 1856919089638522798556275)
                      ·
                        rfl

theorem cell23_3616337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_3616337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616337 prefixEnd_3616337 := by exact prefixLift 3616337
  have htrace : WordTrace (prefixWord ++ tailWord_3616337) baseStart_3616337 baseEnd_3616337 := by
    simpa [prefixWord, tailWord_3616337, baseEnd_3616337] using wordTrace_append hprefix tailTrace_3616337
  have hstable : (prefixWord ++ tailWord_3616337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616337).length < 2 ^ (prefixWord ++ tailWord_3616337).sum := by decide
  have hdescent : baseEnd_3616337 < baseStart_3616337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616343 : List Nat := [1, 1, 3, 2, 2, 4, 1, 9]
def baseStart_3616343 : Nat := 118140960795 + 3616343 * 2 ^ 59
def prefixEnd_3616343 : Nat := 4983230072969 + 3 ^ 40 * 3616343 * 2
def baseEnd_3616343 : Nat := 68774895204535176854861

theorem tailTrace_3616343 : CollatzResearch.WordTrace tailWord_3616343 prefixEnd_3616343 68774895204535176854861 := by
  unfold tailWord_3616343
  simp only [CollatzResearch.WordTrace]
  refine ⟨131898865137614408058093683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87932576758409605372062455 131898865137614408058093683)
  ·
    refine ⟨197848297706421612087140525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131898865137614408058093683 197848297706421612087140525)
    ·
      refine ⟨74193111639908104532677697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197848297706421612087140525 74193111639908104532677697)
      ·
        refine ⟨55644833729931078399508273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74193111639908104532677697 55644833729931078399508273)
        ·
          refine ⟨41733625297448308799631205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55644833729931078399508273 41733625297448308799631205)
          ·
            refine ⟨7825054743271557899930851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41733625297448308799631205 7825054743271557899930851)
            ·
              refine ⟨11737582114907336849896277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825054743271557899930851 11737582114907336849896277)
              ·
                refine ⟨68774895204535176854861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11737582114907336849896277 68774895204535176854861)
                ·
                  rfl

theorem cell23_3616343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 9].length) (baseStart_3616343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616343 prefixEnd_3616343 := by exact prefixLift 3616343
  have htrace : WordTrace (prefixWord ++ tailWord_3616343) baseStart_3616343 baseEnd_3616343 := by
    simpa [prefixWord, tailWord_3616343, baseEnd_3616343] using wordTrace_append hprefix tailTrace_3616343
  have hstable : (prefixWord ++ tailWord_3616343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616343).length < 2 ^ (prefixWord ++ tailWord_3616343).sum := by decide
  have hdescent : baseEnd_3616343 < baseStart_3616343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616357 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3616357 : Nat := 118140960795 + 3616357 * 2 ^ 59
def prefixEnd_3616357 : Nat := 4983230072969 + 3 ^ 40 * 3616357 * 2
def baseEnd_3616357 : Nat := 1856929359251612720306183

theorem tailTrace_3616357 : CollatzResearch.WordTrace tailWord_3616357 prefixEnd_3616357 1856929359251612720306183 := by
  unfold tailWord_3616357
  simp only [CollatzResearch.WordTrace]
  refine ⟨131899375759563688449103325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87932917173042458966068883 131899375759563688449103325)
  ·
    refine ⟨49462265909836383168413747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131899375759563688449103325 49462265909836383168413747)
    ·
      refine ⟨74193398864754574752620621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49462265909836383168413747 74193398864754574752620621)
      ·
        refine ⟨27822524574282965532232733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74193398864754574752620621 27822524574282965532232733)
        ·
          refine ⟨10433446715356112074587275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27822524574282965532232733 10433446715356112074587275)
          ·
            refine ⟨15650170073034168111880913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10433446715356112074587275 15650170073034168111880913)
            ·
              refine ⟨11737627554775626083910685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15650170073034168111880913 11737627554775626083910685)
              ·
                refine ⟨4401610333040859781466507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11737627554775626083910685 4401610333040859781466507)
                ·
                  refine ⟨6602415499561289672199761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401610333040859781466507 6602415499561289672199761)
                  ·
                    refine ⟨4951811624670967254149821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602415499561289672199761 4951811624670967254149821)
                    ·
                      refine ⟨1856929359251612720306183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951811624670967254149821 1856929359251612720306183)
                      ·
                        rfl

theorem cell23_3616357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3616357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616357 prefixEnd_3616357 := by exact prefixLift 3616357
  have htrace : WordTrace (prefixWord ++ tailWord_3616357) baseStart_3616357 baseEnd_3616357 := by
    simpa [prefixWord, tailWord_3616357, baseEnd_3616357] using wordTrace_append hprefix tailTrace_3616357
  have hstable : (prefixWord ++ tailWord_3616357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616357).length < 2 ^ (prefixWord ++ tailWord_3616357).sum := by decide
  have hdescent : baseEnd_3616357 < baseStart_3616357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616360 : List Nat := [2, 1, 4, 3, 1, 3, 9]
def baseStart_3616360 : Nat := 118140960795 + 3616360 * 2 ^ 59
def prefixEnd_3616360 : Nat := 4983230072969 + 3 ^ 40 * 3616360 * 2
def baseEnd_3616360 : Nat := 22925072835723163068749

theorem tailTrace_3616360 : CollatzResearch.WordTrace tailWord_3616360 prefixEnd_3616360 22925072835723163068749 := by
  unfold tailWord_3616360
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949742589276409980731267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87932990119035213307641689 65949742589276409980731267)
  ·
    refine ⟨98924613883914614971096901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65949742589276409980731267 98924613883914614971096901)
    ·
      refine ⟨18548365103233990307080669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98924613883914614971096901 18548365103233990307080669)
      ·
        refine ⟨6955636913712746365155251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18548365103233990307080669 6955636913712746365155251)
        ·
          refine ⟨10433455370569119547732877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955636913712746365155251 10433455370569119547732877)
          ·
            refine ⟨3912545763963419830399829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10433455370569119547732877 3912545763963419830399829)
            ·
              refine ⟨22925072835723163068749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3912545763963419830399829 22925072835723163068749)
              ·
                rfl

theorem cell23_3616360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 9].length) (baseStart_3616360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616360 prefixEnd_3616360 := by exact prefixLift 3616360
  have htrace : WordTrace (prefixWord ++ tailWord_3616360) baseStart_3616360 baseEnd_3616360 := by
    simpa [prefixWord, tailWord_3616360, baseEnd_3616360] using wordTrace_append hprefix tailTrace_3616360
  have hstable : (prefixWord ++ tailWord_3616360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616360).length < 2 ^ (prefixWord ++ tailWord_3616360).sum := by decide
  have hdescent : baseEnd_3616360 < baseStart_3616360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616380 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_3616380 : Nat := 118140960795 + 3616380 * 2 ^ 59
def prefixEnd_3616380 : Nat := 4983230072969 + 3 ^ 40 * 3616380 * 2
def baseEnd_3616380 : Nat := 1856941169306666130318577

theorem tailTrace_3616380 : CollatzResearch.WordTrace tailWord_3616380 prefixEnd_3616380 1856941169306666130318577 := by
  unfold tailWord_3616380
  simp only [CollatzResearch.WordTrace]
  refine ⟨65950107319240181688595297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87933476425653575584793729 65950107319240181688595297)
  ·
    refine ⟨49462580489430136266446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65950107319240181688595297 49462580489430136266446473)
    ·
      refine ⟨37096935367072602199834855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49462580489430136266446473 37096935367072602199834855)
      ·
        refine ⟨55645403050608903299752283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096935367072602199834855 55645403050608903299752283)
        ·
          refine ⟨83468104575913354949628425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55645403050608903299752283 83468104575913354949628425)
          ·
            refine ⟨62601078431935016212221319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83468104575913354949628425 62601078431935016212221319)
            ·
              refine ⟨93901617647902524318331979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62601078431935016212221319 93901617647902524318331979)
              ·
                refine ⟨140852426471853786477497969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93901617647902524318331979 140852426471853786477497969)
                ·
                  refine ⟨105639319853890339858123477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140852426471853786477497969 105639319853890339858123477)
                  ·
                    refine ⟨2475921559075554840424769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105639319853890339858123477 2475921559075554840424769)
                    ·
                      refine ⟨1856941169306666130318577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475921559075554840424769 1856941169306666130318577)
                      ·
                        rfl

theorem cell23_3616380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_3616380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616380 prefixEnd_3616380 := by exact prefixLift 3616380
  have htrace : WordTrace (prefixWord ++ tailWord_3616380) baseStart_3616380 baseEnd_3616380 := by
    simpa [prefixWord, tailWord_3616380, baseEnd_3616380] using wordTrace_append hprefix tailTrace_3616380
  have hstable : (prefixWord ++ tailWord_3616380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616380).length < 2 ^ (prefixWord ++ tailWord_3616380).sum := by decide
  have hdescent : baseEnd_3616380 < baseStart_3616380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616404 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3616404 : Nat := 118140960795 + 3616404 * 2 ^ 59
def prefixEnd_3616404 : Nat := 4983230072969 + 3 ^ 40 * 3616404 * 2
def baseEnd_3616404 : Nat := 1856953492842374036418467

theorem tailTrace_3616404 : CollatzResearch.WordTrace tailWord_3616404 prefixEnd_3616404 1856953492842374036418467 := by
  unfold tailWord_3616404
  simp only [CollatzResearch.WordTrace]
  refine ⟨65950544995196707738032133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87934059993595610317376177 65950544995196707738032133)
  ·
    refine ⟨12365727186599382700881025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65950544995196707738032133 12365727186599382700881025)
    ·
      refine ⟨9274295389949537025660769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12365727186599382700881025 9274295389949537025660769)
      ·
        refine ⟨6955721542462152769245577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9274295389949537025660769 6955721542462152769245577)
        ·
          refine ⟨5216791156846614576934183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6955721542462152769245577 5216791156846614576934183)
          ·
            refine ⟨7825186735269921865401275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216791156846614576934183 7825186735269921865401275)
            ·
              refine ⟨11737780102904882798101913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825186735269921865401275 11737780102904882798101913)
              ·
                refine ⟨8803335077178662098576435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11737780102904882798101913 8803335077178662098576435)
                ·
                  refine ⟨13205002615767993147864653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803335077178662098576435 13205002615767993147864653)
                  ·
                    refine ⟨4951875980912997430449245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13205002615767993147864653 4951875980912997430449245)
                    ·
                      refine ⟨1856953492842374036418467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4951875980912997430449245 1856953492842374036418467)
                      ·
                        rfl

theorem cell23_3616404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3616404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616404 prefixEnd_3616404 := by exact prefixLift 3616404
  have htrace : WordTrace (prefixWord ++ tailWord_3616404) baseStart_3616404 baseEnd_3616404 := by
    simpa [prefixWord, tailWord_3616404, baseEnd_3616404] using wordTrace_append hprefix tailTrace_3616404
  have hstable : (prefixWord ++ tailWord_3616404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616404).length < 2 ^ (prefixWord ++ tailWord_3616404).sum := by decide
  have hdescent : baseEnd_3616404 < baseStart_3616404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616437 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3616437 : Nat := 118140960795 + 3616437 * 2 ^ 59
def prefixEnd_3616437 : Nat := 4983230072969 + 3 ^ 40 * 3616437 * 2
def baseEnd_3616437 : Nat := 618990145901324135768605

theorem tailTrace_3616437 : CollatzResearch.WordTrace tailWord_3616437 prefixEnd_3616437 618990145901324135768605 := by
  unfold tailWord_3616437
  simp only [CollatzResearch.WordTrace]
  refine ⟨131902293599273862112015565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87934862399515908074677043 131902293599273862112015565)
  ·
    refine ⟨49463360099727698292005837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131902293599273862112015565 49463360099727698292005837)
    ·
      refine ⟨18548760037397886859502189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49463360099727698292005837 18548760037397886859502189)
      ·
        refine ⟨6955785014024207572313321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18548760037397886859502189 6955785014024207572313321)
        ·
          refine ⟨5216838760518155679234991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6955785014024207572313321 5216838760518155679234991)
          ·
            refine ⟨7825258140777233518852487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216838760518155679234991 7825258140777233518852487)
            ·
              refine ⟨11737887211165850278278731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825258140777233518852487 11737887211165850278278731)
              ·
                refine ⟨17606830816748775417418097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11737887211165850278278731 17606830816748775417418097)
                ·
                  refine ⟨13205123112561581563063573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17606830816748775417418097 13205123112561581563063573)
                  ·
                    refine ⟨618990145901324135768605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13205123112561581563063573 618990145901324135768605)
                    ·
                      rfl

theorem cell23_3616437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3616437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616437 prefixEnd_3616437 := by exact prefixLift 3616437
  have htrace : WordTrace (prefixWord ++ tailWord_3616437) baseStart_3616437 baseEnd_3616437 := by
    simpa [prefixWord, tailWord_3616437, baseEnd_3616437] using wordTrace_append hprefix tailTrace_3616437
  have hstable : (prefixWord ++ tailWord_3616437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616437).length < 2 ^ (prefixWord ++ tailWord_3616437).sum := by decide
  have hdescent : baseEnd_3616437 < baseStart_3616437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616444 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3616444 : Nat := 118140960795 + 3616444 * 2 ^ 59
def prefixEnd_3616444 : Nat := 4983230072969 + 3 ^ 40 * 3616444 * 2
def baseEnd_3616444 : Nat := 1856974032068553879918283

theorem tailTrace_3616444 : CollatzResearch.WordTrace tailWord_3616444 prefixEnd_3616444 1856974032068553879918283 := by
  unfold tailWord_3616444
  simp only [CollatzResearch.WordTrace]
  refine ⟨65951274455124251153760193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87935032606832334871680257 65951274455124251153760193)
  ·
    refine ⟨49463455841343188365320145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65951274455124251153760193 49463455841343188365320145)
    ·
      refine ⟨37097591881007391273990109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49463455841343188365320145 37097591881007391273990109)
      ·
        refine ⟨13911596955377771727746291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37097591881007391273990109 13911596955377771727746291)
        ·
          refine ⟨20867395433066657591619437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13911596955377771727746291 20867395433066657591619437)
          ·
            refine ⟨7825273287399996596857289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20867395433066657591619437 7825273287399996596857289)
            ·
              refine ⟨5868954965549997447642967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825273287399996596857289 5868954965549997447642967)
              ·
                refine ⟨8803432448324996171464451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868954965549997447642967 8803432448324996171464451)
                ·
                  refine ⟨13205148672487494257196677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803432448324996171464451 13205148672487494257196677)
                  ·
                    refine ⟨2475965376091405173224377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13205148672487494257196677 2475965376091405173224377)
                    ·
                      refine ⟨1856974032068553879918283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475965376091405173224377 1856974032068553879918283)
                      ·
                        rfl

theorem cell23_3616444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3616444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616444 prefixEnd_3616444 := by exact prefixLift 3616444
  have htrace : WordTrace (prefixWord ++ tailWord_3616444) baseStart_3616444 baseEnd_3616444 := by
    simpa [prefixWord, tailWord_3616444, baseEnd_3616444] using wordTrace_append hprefix tailTrace_3616444
  have hstable : (prefixWord ++ tailWord_3616444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616444).length < 2 ^ (prefixWord ++ tailWord_3616444).sum := by decide
  have hdescent : baseEnd_3616444 < baseStart_3616444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616453 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3616453 : Nat := 118140960795 + 3616453 * 2 ^ 59
def prefixEnd_3616453 : Nat := 4983230072969 + 3 ^ 40 * 3616453 * 2
def baseEnd_3616453 : Nat := 1856978653394444344705741

theorem tailTrace_3616453 : CollatzResearch.WordTrace tailWord_3616453 prefixEnd_3616453 1856978653394444344705741 := by
  unfold tailWord_3616453
  simp only [CollatzResearch.WordTrace]
  refine ⟨131902877167215896844598013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87935251444810597896398675 131902877167215896844598013)
  ·
    refine ⟨49463578937705961316724255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131902877167215896844598013 49463578937705961316724255)
    ·
      refine ⟨74195368406558941975086383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49463578937705961316724255 74195368406558941975086383)
      ·
        refine ⟨111293052609838412962629575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74195368406558941975086383 111293052609838412962629575)
        ·
          refine ⟨166939578914757619443944363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111293052609838412962629575 166939578914757619443944363)
          ·
            refine ⟨250409368372136429165916545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166939578914757619443944363 250409368372136429165916545)
            ·
              refine ⟨187807026279102321874437409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250409368372136429165916545 187807026279102321874437409)
              ·
                refine ⟨140855269709326741405828057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187807026279102321874437409 140855269709326741405828057)
                ·
                  refine ⟨105641452281995056054371043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140855269709326741405828057 105641452281995056054371043)
                  ·
                    refine ⟨158462178422992584081556565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105641452281995056054371043 158462178422992584081556565)
                    ·
                      refine ⟨1856978653394444344705741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 158462178422992584081556565 1856978653394444344705741)
                      ·
                        rfl

theorem cell23_3616453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3616453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616453 prefixEnd_3616453 := by exact prefixLift 3616453
  have htrace : WordTrace (prefixWord ++ tailWord_3616453) baseStart_3616453 baseEnd_3616453 := by
    simpa [prefixWord, tailWord_3616453, baseEnd_3616453] using wordTrace_append hprefix tailTrace_3616453
  have hstable : (prefixWord ++ tailWord_3616453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616453).length < 2 ^ (prefixWord ++ tailWord_3616453).sum := by decide
  have hdescent : baseEnd_3616453 < baseStart_3616453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616461 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3616461 : Nat := 118140960795 + 3616461 * 2 ^ 59
def prefixEnd_3616461 : Nat := 4983230072969 + 3 ^ 40 * 3616461 * 2
def baseEnd_3616461 : Nat := 1856982761239680313405705

theorem tailTrace_3616461 : CollatzResearch.WordTrace tailWord_3616461 prefixEnd_3616461 1856982761239680313405705 := by
  unfold tailWord_3616461
  simp only [CollatzResearch.WordTrace]
  refine ⟨131903168951186914210889237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87935445967457942807259491 131903168951186914210889237)
  ·
    refine ⟨6182961044586886603635433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131903168951186914210889237 6182961044586886603635433)
    ·
      refine ⟨4637220783440164952726575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6182961044586886603635433 4637220783440164952726575)
      ·
        refine ⟨6955831175160247429089863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637220783440164952726575 6955831175160247429089863)
        ·
          refine ⟨10433746762740371143634795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955831175160247429089863 10433746762740371143634795)
          ·
            refine ⟨15650620144110556715452193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10433746762740371143634795 15650620144110556715452193)
            ·
              refine ⟨11737965108082917536589145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15650620144110556715452193 11737965108082917536589145)
              ·
                refine ⟨8803473831062188152441859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11737965108082917536589145 8803473831062188152441859)
                ·
                  refine ⟨13205210746593282228662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803473831062188152441859 13205210746593282228662789)
                  ·
                    refine ⟨2475977014986240417874273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13205210746593282228662789 2475977014986240417874273)
                    ·
                      refine ⟨1856982761239680313405705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2475977014986240417874273 1856982761239680313405705)
                      ·
                        rfl

theorem cell23_3616461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3616461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616461 prefixEnd_3616461 := by exact prefixLift 3616461
  have htrace : WordTrace (prefixWord ++ tailWord_3616461) baseStart_3616461 baseEnd_3616461 := by
    simpa [prefixWord, tailWord_3616461, baseEnd_3616461] using wordTrace_append hprefix tailTrace_3616461
  have hstable : (prefixWord ++ tailWord_3616461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616461).length < 2 ^ (prefixWord ++ tailWord_3616461).sum := by decide
  have hdescent : baseEnd_3616461 < baseStart_3616461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616480 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_3616480 : Nat := 118140960795 + 3616480 * 2 ^ 59
def prefixEnd_3616480 : Nat := 4983230072969 + 3 ^ 40 * 3616480 * 2
def baseEnd_3616480 : Nat := 618997505790705246356039

theorem tailTrace_3616480 : CollatzResearch.WordTrace tailWord_3616480 prefixEnd_3616480 618997505790705246356039 := by
  unfold tailWord_3616480
  simp only [CollatzResearch.WordTrace]
  refine ⟨65951930969059040227915447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87935907958745386970553929 65951930969059040227915447)
  ·
    refine ⟨98927896453588560341873171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65951930969059040227915447 98927896453588560341873171)
    ·
      refine ⟨148391844680382840512809757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98927896453588560341873171 148391844680382840512809757)
      ·
        refine ⟨55646941755143565192303659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148391844680382840512809757 55646941755143565192303659)
        ·
          refine ⟨83470412632715347788455489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55646941755143565192303659 83470412632715347788455489)
          ·
            refine ⟨62602809474536510841341617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83470412632715347788455489 62602809474536510841341617)
            ·
              refine ⟨46952107105902383131006213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62602809474536510841341617 46952107105902383131006213)
              ·
                refine ⟨8803520082356696837063665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46952107105902383131006213 8803520082356696837063665)
                ·
                  refine ⟨6602640061767522627797749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8803520082356696837063665 6602640061767522627797749)
                  ·
                    refine ⟨618997505790705246356039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6602640061767522627797749 618997505790705246356039)
                    ·
                      rfl

theorem cell23_3616480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_3616480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616480 prefixEnd_3616480 := by exact prefixLift 3616480
  have htrace : WordTrace (prefixWord ++ tailWord_3616480) baseStart_3616480 baseEnd_3616480 := by
    simpa [prefixWord, tailWord_3616480, baseEnd_3616480] using wordTrace_append hprefix tailTrace_3616480
  have hstable : (prefixWord ++ tailWord_3616480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616480).length < 2 ^ (prefixWord ++ tailWord_3616480).sum := by decide
  have hdescent : baseEnd_3616480 < baseStart_3616480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616490 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3616490 : Nat := 118140960795 + 3616490 * 2 ^ 59
def prefixEnd_3616490 : Nat := 4983230072969 + 3 ^ 40 * 3616490 * 2
def baseEnd_3616490 : Nat := 1856997652178660699943071

theorem tailTrace_3616490 : CollatzResearch.WordTrace tailWord_3616490 prefixEnd_3616490 1856997652178660699943071 := by
  unfold tailWord_3616490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32976056667020463040923731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87936151112054568109129949 32976056667020463040923731)
  ·
    refine ⟨49464085000530694561385597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32976056667020463040923731 49464085000530694561385597)
    ·
      refine ⟨18549031875199010460519599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49464085000530694561385597 18549031875199010460519599)
      ·
        refine ⟨27823547812798515690779399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549031875199010460519599 27823547812798515690779399)
        ·
          refine ⟨41735321719197773536169099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27823547812798515690779399 41735321719197773536169099)
          ·
            refine ⟨62602982578796660304253649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41735321719197773536169099 62602982578796660304253649)
            ·
              refine ⟨46952236934097495228190237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62602982578796660304253649 46952236934097495228190237)
              ·
                refine ⟨17607088850286560710571339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46952236934097495228190237 17607088850286560710571339)
                ·
                  refine ⟨26410633275429841065857009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17607088850286560710571339 26410633275429841065857009)
                  ·
                    refine ⟨19807974956572380799392757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26410633275429841065857009 19807974956572380799392757)
                    ·
                      refine ⟨1856997652178660699943071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19807974956572380799392757 1856997652178660699943071)
                      ·
                        rfl

theorem cell23_3616490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3616490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616490 prefixEnd_3616490 := by exact prefixLift 3616490
  have htrace : WordTrace (prefixWord ++ tailWord_3616490) baseStart_3616490 baseEnd_3616490 := by
    simpa [prefixWord, tailWord_3616490, baseEnd_3616490] using wordTrace_append hprefix tailTrace_3616490
  have hstable : (prefixWord ++ tailWord_3616490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616490).length < 2 ^ (prefixWord ++ tailWord_3616490).sum := by decide
  have hdescent : baseEnd_3616490 < baseStart_3616490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616540 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 8]
def baseStart_3616540 : Nat := 118140960795 + 3616540 * 2 ^ 59
def prefixEnd_3616540 : Nat := 4983230072969 + 3 ^ 40 * 3616540 * 2
def baseEnd_3616540 : Nat := 206335925134598389368649

theorem tailTrace_3616540 : CollatzResearch.WordTrace tailWord_3616540 prefixEnd_3616540 206335925134598389368649 := by
  unfold tailWord_3616540
  simp only [CollatzResearch.WordTrace]
  refine ⟨65953025158950355351507537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87937366878600473802010049 65953025158950355351507537)
  ·
    refine ⟨49464768869212766513630653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65953025158950355351507537 49464768869212766513630653)
    ·
      refine ⟨18549288325954787442611495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49464768869212766513630653 18549288325954787442611495)
      ·
        refine ⟨27823932488932181163917243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549288325954787442611495 27823932488932181163917243)
        ·
          refine ⟨41735898733398271745875865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27823932488932181163917243 41735898733398271745875865)
          ·
            refine ⟨31301924050048703809406899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41735898733398271745875865 31301924050048703809406899)
            ·
              refine ⟨46952886075073055714110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31301924050048703809406899 46952886075073055714110349)
              ·
                refine ⟨17607332278152395892791381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46952886075073055714110349 17607332278152395892791381)
                ·
                  refine ⟨206335925134598389368649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17607332278152395892791381 206335925134598389368649)
                  ·
                    rfl

theorem cell23_3616540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_3616540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616540 prefixEnd_3616540 := by exact prefixLift 3616540
  have htrace : WordTrace (prefixWord ++ tailWord_3616540) baseStart_3616540 baseEnd_3616540 := by
    simpa [prefixWord, tailWord_3616540, baseEnd_3616540] using wordTrace_append hprefix tailTrace_3616540
  have hstable : (prefixWord ++ tailWord_3616540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616540).length < 2 ^ (prefixWord ++ tailWord_3616540).sum := by decide
  have hdescent : baseEnd_3616540 < baseStart_3616540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616601 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 1, 1, 3]
def baseStart_3616601 : Nat := 118140960795 + 3616601 * 2 ^ 59
def prefixEnd_3616601 : Nat := 4983230072969 + 3 ^ 40 * 3616601 * 2
def baseEnd_3616601 : Nat := 1857054648531309765655061

theorem tailTrace_3616601 : CollatzResearch.WordTrace tailWord_3616601 prefixEnd_3616601 1857054648531309765655061 := by
  unfold tailWord_3616601
  simp only [CollatzResearch.WordTrace]
  refine ⟨131908275170679718120985657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87938850113786478747323771 131908275170679718120985657)
  ·
    refine ⟨98931206378009788590739243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131908275170679718120985657 98931206378009788590739243)
    ·
      refine ⟨148396809567014682886108865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98931206378009788590739243 148396809567014682886108865)
      ·
        refine ⟨111297607175261012164581649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148396809567014682886108865 111297607175261012164581649)
        ·
          refine ⟨83473205381445759123436237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111297607175261012164581649 83473205381445759123436237)
          ·
            refine ⟨31302452018042159671288589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83473205381445759123436237 31302452018042159671288589)
            ·
              refine ⟨11738419506765809876733221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31302452018042159671288589 11738419506765809876733221)
              ·
                refine ⟨2200953657518589351887479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11738419506765809876733221 2200953657518589351887479)
                ·
                  refine ⟨3301430486277884027831219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200953657518589351887479 3301430486277884027831219)
                  ·
                    refine ⟨4952145729416826041746829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301430486277884027831219 4952145729416826041746829)
                    ·
                      refine ⟨1857054648531309765655061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952145729416826041746829 1857054648531309765655061)
                      ·
                        rfl

theorem cell23_3616601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_3616601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616601 prefixEnd_3616601 := by exact prefixLift 3616601
  have htrace : WordTrace (prefixWord ++ tailWord_3616601) baseStart_3616601 baseEnd_3616601 := by
    simpa [prefixWord, tailWord_3616601, baseEnd_3616601] using wordTrace_append hprefix tailTrace_3616601
  have hstable : (prefixWord ++ tailWord_3616601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616601).length < 2 ^ (prefixWord ++ tailWord_3616601).sum := by decide
  have hdescent : baseEnd_3616601 < baseStart_3616601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616607 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_3616607 : Nat := 118140960795 + 3616607 * 2 ^ 59
def prefixEnd_3616607 : Nat := 4983230072969 + 3 ^ 40 * 3616607 * 2
def baseEnd_3616607 : Nat := 1857057729415236742180033

theorem tailTrace_3616607 : CollatzResearch.WordTrace tailWord_3616607 prefixEnd_3616607 1857057729415236742180033 := by
  unfold tailWord_3616607
  simp only [CollatzResearch.WordTrace]
  refine ⟨131908494008657981145704075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87938996005771987430469383 131908494008657981145704075)
  ·
    refine ⟨197862741012986971718556113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131908494008657981145704075 197862741012986971718556113)
    ·
      refine ⟨148397055759740228788917085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197862741012986971718556113 148397055759740228788917085)
      ·
        refine ⟨55648895909902585795843907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148397055759740228788917085 55648895909902585795843907)
        ·
          refine ⟨83473343864853878693765861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55648895909902585795843907 83473343864853878693765861)
          ·
            refine ⟨15651251974660102255081099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83473343864853878693765861 15651251974660102255081099)
            ·
              refine ⟨23476877961990153382621649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651251974660102255081099 23476877961990153382621649)
              ·
                refine ⟨17607658471492615036966237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23476877961990153382621649 17607658471492615036966237)
                ·
                  refine ⟨6602871926809730638862339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17607658471492615036966237 6602871926809730638862339)
                  ·
                    refine ⟨9904307890214595958293509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6602871926809730638862339 9904307890214595958293509)
                    ·
                      refine ⟨1857057729415236742180033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9904307890214595958293509 1857057729415236742180033)
                      ·
                        rfl

theorem cell23_3616607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_3616607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616607 prefixEnd_3616607 := by exact prefixLift 3616607
  have htrace : WordTrace (prefixWord ++ tailWord_3616607) baseStart_3616607 baseEnd_3616607 := by
    simpa [prefixWord, tailWord_3616607, baseEnd_3616607] using wordTrace_append hprefix tailTrace_3616607
  have hstable : (prefixWord ++ tailWord_3616607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616607).length < 2 ^ (prefixWord ++ tailWord_3616607).sum := by decide
  have hdescent : baseEnd_3616607 < baseStart_3616607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616618 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3616618 : Nat := 118140960795 + 3616618 * 2 ^ 59
def prefixEnd_3616618 : Nat := 4983230072969 + 3 ^ 40 * 3616618 * 2
def baseEnd_3616618 : Nat := 1857063377702436199142483

theorem tailTrace_3616618 : CollatzResearch.WordTrace tailWord_3616618 prefixEnd_3616618 1857063377702436199142483 := by
  unfold tailWord_3616618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977223802904532506088627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87939263474412086682903005 32977223802904532506088627)
  ·
    refine ⟨49465835704356798759132941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977223802904532506088627 49465835704356798759132941)
    ·
      refine ⟨18549688389133799534674853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49465835704356798759132941 18549688389133799534674853)
      ·
        refine ⟨3478066572962587412751535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18549688389133799534674853 3478066572962587412751535)
        ·
          refine ⟨5217099859443881119127303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478066572962587412751535 5217099859443881119127303)
          ·
            refine ⟨7825649789165821678690955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217099859443881119127303 7825649789165821678690955)
            ·
              refine ⟨11738474683748732518036433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825649789165821678690955 11738474683748732518036433)
              ·
                refine ⟨8803856012811549388527325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11738474683748732518036433 8803856012811549388527325)
                ·
                  refine ⟨3301446004804331020697747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8803856012811549388527325 3301446004804331020697747)
                  ·
                    refine ⟨4952169007206496531046621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301446004804331020697747 4952169007206496531046621)
                    ·
                      refine ⟨1857063377702436199142483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952169007206496531046621 1857063377702436199142483)
                      ·
                        rfl

theorem cell23_3616618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3616618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616618 prefixEnd_3616618 := by exact prefixLift 3616618
  have htrace : WordTrace (prefixWord ++ tailWord_3616618) baseStart_3616618 baseEnd_3616618 := by
    simpa [prefixWord, tailWord_3616618, baseEnd_3616618] using wordTrace_append hprefix tailTrace_3616618
  have hstable : (prefixWord ++ tailWord_3616618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616618).length < 2 ^ (prefixWord ++ tailWord_3616618).sum := by decide
  have hdescent : baseEnd_3616618 < baseStart_3616618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616638 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3616638 : Nat := 118140960795 + 3616638 * 2 ^ 59
def prefixEnd_3616638 : Nat := 4983230072969 + 3 ^ 40 * 3616638 * 2
def baseEnd_3616638 : Nat := 619024549105175373630797

theorem tailTrace_3616638 : CollatzResearch.WordTrace tailWord_3616638 prefixEnd_3616638 619024549105175373630797 := by
  unfold tailWord_3616638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488703083943209180010321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87939749781030448960055045 16488703083943209180010321)
  ·
    refine ⟨12366527312957406885007741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16488703083943209180010321 12366527312957406885007741)
    ·
      refine ⟨4637447742359027581877903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12366527312957406885007741 4637447742359027581877903)
      ·
        refine ⟨6956171613538541372816855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637447742359027581877903 6956171613538541372816855)
        ·
          refine ⟨10434257420307812059225283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956171613538541372816855 10434257420307812059225283)
          ·
            refine ⟨15651386130461718088837925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434257420307812059225283 15651386130461718088837925)
            ·
              refine ⟨2934634899461572141657111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15651386130461718088837925 2934634899461572141657111)
              ·
                refine ⟨4401952349192358212485667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934634899461572141657111 4401952349192358212485667)
                ·
                  refine ⟨6602928523788537318728501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401952349192358212485667 6602928523788537318728501)
                  ·
                    refine ⟨619024549105175373630797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6602928523788537318728501 619024549105175373630797)
                    ·
                      rfl

theorem cell23_3616638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3616638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616638 prefixEnd_3616638 := by exact prefixLift 3616638
  have htrace : WordTrace (prefixWord ++ tailWord_3616638) baseStart_3616638 baseEnd_3616638 := by
    simpa [prefixWord, tailWord_3616638, baseEnd_3616638] using wordTrace_append hprefix tailTrace_3616638
  have hstable : (prefixWord ++ tailWord_3616638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616638).length < 2 ^ (prefixWord ++ tailWord_3616638).sum := by decide
  have hdescent : baseEnd_3616638 < baseStart_3616638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616647 : List Nat := [1, 1, 4, 2, 4, 1, 10]
def baseStart_3616647 : Nat := 118140960795 + 3616647 * 2 ^ 59
def prefixEnd_3616647 : Nat := 4983230072969 + 3 ^ 40 * 3616647 * 2
def baseEnd_3616647 : Nat := 22926892205449587477529

theorem tailTrace_3616647 : CollatzResearch.WordTrace tailWord_3616647 prefixEnd_3616647 22926892205449587477529 := by
  unfold tailWord_3616647
  simp only [CollatzResearch.WordTrace]
  refine ⟨131909952928513067977160195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87939968619008711984773463 131909952928513067977160195)
  ·
    refine ⟨197864929392769601965740293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131909952928513067977160195 197864929392769601965740293)
    ·
      refine ⟨37099674261144300368576305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197864929392769601965740293 37099674261144300368576305)
      ·
        refine ⟨27824755695858225276432229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37099674261144300368576305 27824755695858225276432229)
        ·
          refine ⟨5217141692973417239331043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27824755695858225276432229 5217141692973417239331043)
          ·
            refine ⟨7825712539460125858996565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217141692973417239331043 7825712539460125858996565)
            ·
              refine ⟨22926892205449587477529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7825712539460125858996565 22926892205449587477529)
              ·
                rfl

theorem cell23_3616647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 10].length) (baseStart_3616647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616647 prefixEnd_3616647 := by exact prefixLift 3616647
  have htrace : WordTrace (prefixWord ++ tailWord_3616647) baseStart_3616647 baseEnd_3616647 := by
    simpa [prefixWord, tailWord_3616647, baseEnd_3616647] using wordTrace_append hprefix tailTrace_3616647
  have hstable : (prefixWord ++ tailWord_3616647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616647).length < 2 ^ (prefixWord ++ tailWord_3616647).sum := by decide
  have hdescent : baseEnd_3616647 < baseStart_3616647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616657 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_3616657 : Nat := 118140960795 + 3616657 * 2 ^ 59
def prefixEnd_3616657 : Nat := 4983230072969 + 3 ^ 40 * 3616657 * 2
def baseEnd_3616657 : Nat := 1857083403447961546554803

theorem tailTrace_3616657 : CollatzResearch.WordTrace tailWord_3616657 prefixEnd_3616657 1857083403447961546554803 := by
  unfold tailWord_3616657
  simp only [CollatzResearch.WordTrace]
  refine ⟨131910317658476839685024225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87940211772317893123349483 131910317658476839685024225)
  ·
    refine ⟨98932738243857629763768169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131910317658476839685024225 98932738243857629763768169)
    ·
      refine ⟨74199553682893222322826127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98932738243857629763768169 74199553682893222322826127)
      ·
        refine ⟨111299330524339833484239191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74199553682893222322826127 111299330524339833484239191)
        ·
          refine ⟨166948995786509750226358787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111299330524339833484239191 166948995786509750226358787)
          ·
            refine ⟨250423493679764625339538181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166948995786509750226358787 250423493679764625339538181)
            ·
              refine ⟨46954405064955867251163409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250423493679764625339538181 46954405064955867251163409)
              ·
                refine ⟨35215803798716900438372557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46954405064955867251163409 35215803798716900438372557)
                ·
                  refine ⟨13205926424518837664389709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35215803798716900438372557 13205926424518837664389709)
                  ·
                    refine ⟨4952222409194564124146141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13205926424518837664389709 4952222409194564124146141)
                    ·
                      refine ⟨1857083403447961546554803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952222409194564124146141 1857083403447961546554803)
                      ·
                        rfl

theorem cell23_3616657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_3616657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616657 prefixEnd_3616657 := by exact prefixLift 3616657
  have htrace : WordTrace (prefixWord ++ tailWord_3616657) baseStart_3616657 baseEnd_3616657 := by
    simpa [prefixWord, tailWord_3616657, baseEnd_3616657] using wordTrace_append hprefix tailTrace_3616657
  have hstable : (prefixWord ++ tailWord_3616657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616657).length < 2 ^ (prefixWord ++ tailWord_3616657).sum := by decide
  have hdescent : baseEnd_3616657 < baseStart_3616657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616658 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3616658 : Nat := 118140960795 + 3616658 * 2 ^ 59
def prefixEnd_3616658 : Nat := 4983230072969 + 3 ^ 40 * 3616658 * 2
def baseEnd_3616658 : Nat := 1857083916928616042642299

theorem tailTrace_3616658 : CollatzResearch.WordTrace tailWord_3616658 prefixEnd_3616658 1857083916928616042642299 := by
  unfold tailWord_3616658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977588532868304213952657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87940236087648811237207085 32977588532868304213952657)
  ·
    refine ⟨24733191399651228160464493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32977588532868304213952657 24733191399651228160464493)
    ·
      refine ⟨9274946774869210560174185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24733191399651228160464493 9274946774869210560174185)
      ·
        refine ⟨6956210081151907920130639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9274946774869210560174185 6956210081151907920130639)
        ·
          refine ⟨10434315121727861880195959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956210081151907920130639 10434315121727861880195959)
          ·
            refine ⟨15651472682591792820293939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434315121727861880195959 15651472682591792820293939)
            ·
              refine ⟨23477209023887689230440909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651472682591792820293939 23477209023887689230440909)
              ·
                refine ⟨8803953383957883461415341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23477209023887689230440909 8803953383957883461415341)
                ·
                  refine ⟨3301482518984206298030753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8803953383957883461415341 3301482518984206298030753)
                  ·
                    refine ⟨2476111889238154723523065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3301482518984206298030753 2476111889238154723523065)
                    ·
                      refine ⟨1857083916928616042642299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476111889238154723523065 1857083916928616042642299)
                      ·
                        rfl

theorem cell23_3616658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3616658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616658 prefixEnd_3616658 := by exact prefixLift 3616658
  have htrace : WordTrace (prefixWord ++ tailWord_3616658) baseStart_3616658 baseEnd_3616658 := by
    simpa [prefixWord, tailWord_3616658, baseEnd_3616658] using wordTrace_append hprefix tailTrace_3616658
  have hstable : (prefixWord ++ tailWord_3616658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616658).length < 2 ^ (prefixWord ++ tailWord_3616658).sum := by decide
  have hdescent : baseEnd_3616658 < baseStart_3616658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616668 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_3616668 : Nat := 118140960795 + 3616668 * 2 ^ 59
def prefixEnd_3616668 : Nat := 4983230072969 + 3 ^ 40 * 3616668 * 2
def baseEnd_3616668 : Nat := 619029683911720334505751

theorem tailTrace_3616668 : CollatzResearch.WordTrace tailWord_3616668 prefixEnd_3616668 619029683911720334505751 := by
  unfold tailWord_3616668
  simp only [CollatzResearch.WordTrace]
  refine ⟨65955359430718494281837329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87940479240957992375783105 65955359430718494281837329)
  ·
    refine ⟨49466519573038870711377997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65955359430718494281837329 49466519573038870711377997)
    ·
      refine ⟨18549944839889576516766749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49466519573038870711377997 18549944839889576516766749)
      ·
        refine ⟨6956229314958591193787531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18549944839889576516766749 6956229314958591193787531)
        ·
          refine ⟨10434343972437886790681297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956229314958591193787531 10434343972437886790681297)
          ·
            refine ⟨7825757979328415093010973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10434343972437886790681297 7825757979328415093010973)
            ·
              refine ⟨2934659242248155659879115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7825757979328415093010973 2934659242248155659879115)
              ·
                refine ⟨4401988863372233489818673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934659242248155659879115 4401988863372233489818673)
                ·
                  refine ⟨3301491647529175117364005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4401988863372233489818673 3301491647529175117364005)
                  ·
                    refine ⟨619029683911720334505751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301491647529175117364005 619029683911720334505751)
                    ·
                      rfl

theorem cell23_3616668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_3616668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616668 prefixEnd_3616668 := by exact prefixLift 3616668
  have htrace : WordTrace (prefixWord ++ tailWord_3616668) baseStart_3616668 baseEnd_3616668 := by
    simpa [prefixWord, tailWord_3616668, baseEnd_3616668] using wordTrace_append hprefix tailTrace_3616668
  have hstable : (prefixWord ++ tailWord_3616668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616668).length < 2 ^ (prefixWord ++ tailWord_3616668).sum := by decide
  have hdescent : baseEnd_3616668 < baseStart_3616668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616671 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3616671 : Nat := 118140960795 + 3616671 * 2 ^ 59
def prefixEnd_3616671 : Nat := 4983230072969 + 3 ^ 40 * 3616671 * 2
def baseEnd_3616671 : Nat := 1857090592177124491779739

theorem tailTrace_3616671 : CollatzResearch.WordTrace tailWord_3616671 prefixEnd_3616671 1857090592177124491779739 := by
  unfold tailWord_3616671
  simp only [CollatzResearch.WordTrace]
  refine ⟨131910828280426120076033867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87940552186950746717355911 131910828280426120076033867)
  ·
    refine ⟨197866242420639180114050801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131910828280426120076033867 197866242420639180114050801)
    ·
      refine ⟨148399681815479385085538101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197866242420639180114050801 148399681815479385085538101)
      ·
        refine ⟨13912470170201192351769197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148399681815479385085538101 13912470170201192351769197)
        ·
          refine ⟨5217176313825447131913449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13912470170201192351769197 5217176313825447131913449)
          ·
            refine ⟨3912882235369085348935087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217176313825447131913449 3912882235369085348935087)
            ·
              refine ⟨5869323353053628023402631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912882235369085348935087 5869323353053628023402631)
              ·
                refine ⟨8803985029580442035103947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869323353053628023402631 8803985029580442035103947)
                ·
                  refine ⟨13205977544370663052655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8803985029580442035103947 13205977544370663052655921)
                  ·
                    refine ⟨9904483158277997289491941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13205977544370663052655921 9904483158277997289491941)
                    ·
                      refine ⟨1857090592177124491779739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9904483158277997289491941 1857090592177124491779739)
                      ·
                        rfl

theorem cell23_3616671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3616671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616671 prefixEnd_3616671 := by exact prefixLift 3616671
  have htrace : WordTrace (prefixWord ++ tailWord_3616671) baseStart_3616671 baseEnd_3616671 := by
    simpa [prefixWord, tailWord_3616671, baseEnd_3616671] using wordTrace_append hprefix tailTrace_3616671
  have hstable : (prefixWord ++ tailWord_3616671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616671).length < 2 ^ (prefixWord ++ tailWord_3616671).sum := by decide
  have hdescent : baseEnd_3616671 < baseStart_3616671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616686 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3616686 : Nat := 118140960795 + 3616686 * 2 ^ 59
def prefixEnd_3616686 : Nat := 4983230072969 + 3 ^ 40 * 3616686 * 2
def baseEnd_3616686 : Nat := 1857098294386941933092171

theorem tailTrace_3616686 : CollatzResearch.WordTrace tailWord_3616686 prefixEnd_3616686 1857098294386941933092171 := by
  unfold tailWord_3616686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488921921921472204728739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87940916916914518425219941 16488921921921472204728739)
  ·
    refine ⟨24733382882882208307093109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16488921921921472204728739 24733382882882208307093109)
    ·
      refine ⟨2318754645270207028789979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24733382882882208307093109 2318754645270207028789979)
      ·
        refine ⟨3478131967905310543184969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318754645270207028789979 3478131967905310543184969)
        ·
          refine ⟨2608598975928982907388727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478131967905310543184969 2608598975928982907388727)
          ·
            refine ⟨3912898463893474361083091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608598975928982907388727 3912898463893474361083091)
            ·
              refine ⟨5869347695840211541624637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912898463893474361083091 5869347695840211541624637)
              ·
                refine ⟨2201005385940079328109239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5869347695840211541624637 2201005385940079328109239)
                ·
                  refine ⟨3301508078910118992163859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201005385940079328109239 3301508078910118992163859)
                  ·
                    refine ⟨4952262118365178488245789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301508078910118992163859 4952262118365178488245789)
                    ·
                      refine ⟨1857098294386941933092171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952262118365178488245789 1857098294386941933092171)
                      ·
                        rfl

theorem cell23_3616686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3616686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616686 prefixEnd_3616686 := by exact prefixLift 3616686
  have htrace : WordTrace (prefixWord ++ tailWord_3616686) baseStart_3616686 baseEnd_3616686 := by
    simpa [prefixWord, tailWord_3616686, baseEnd_3616686] using wordTrace_append hprefix tailTrace_3616686
  have hstable : (prefixWord ++ tailWord_3616686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616686).length < 2 ^ (prefixWord ++ tailWord_3616686).sum := by decide
  have hdescent : baseEnd_3616686 < baseStart_3616686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616725 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3616725 : Nat := 118140960795 + 3616725 * 2 ^ 59
def prefixEnd_3616725 : Nat := 4983230072969 + 3 ^ 40 * 3616725 * 2
def baseEnd_3616725 : Nat := 1857118320132467280504491

theorem tailTrace_3616725 : CollatzResearch.WordTrace tailWord_3616725 prefixEnd_3616725 1857118320132467280504491 := by
  unfold tailWord_3616725
  simp only [CollatzResearch.WordTrace]
  refine ⟨131912797822230487298499629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87941865214820324865666419 131912797822230487298499629)
  ·
    refine ⟨49467299183336432736937361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131912797822230487298499629 49467299183336432736937361)
    ·
      refine ⟨37100474387502324552703021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49467299183336432736937361 37100474387502324552703021)
      ·
        refine ⟨13912677895313371707263633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37100474387502324552703021 13912677895313371707263633)
        ·
          refine ⟨10434508421485028780447725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13912677895313371707263633 10434508421485028780447725)
          ·
            refine ⟨3912940658056885792667897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10434508421485028780447725 3912940658056885792667897)
            ·
              refine ⟨2934705493542664344500923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912940658056885792667897 2934705493542664344500923)
              ·
                refine ⟨4402058240313996516751385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934705493542664344500923 4402058240313996516751385)
                ·
                  refine ⟨3301543680235497387563539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402058240313996516751385 3301543680235497387563539)
                  ·
                    refine ⟨4952315520353246081345309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301543680235497387563539 4952315520353246081345309)
                    ·
                      refine ⟨1857118320132467280504491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952315520353246081345309 1857118320132467280504491)
                      ·
                        rfl

theorem cell23_3616725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3616725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616725 prefixEnd_3616725 := by exact prefixLift 3616725
  have htrace : WordTrace (prefixWord ++ tailWord_3616725) baseStart_3616725 baseEnd_3616725 := by
    simpa [prefixWord, tailWord_3616725, baseEnd_3616725] using wordTrace_append hprefix tailTrace_3616725
  have hstable : (prefixWord ++ tailWord_3616725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616725).length < 2 ^ (prefixWord ++ tailWord_3616725).sum := by decide
  have hdescent : baseEnd_3616725 < baseStart_3616725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616727 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3616727 : Nat := 118140960795 + 3616727 * 2 ^ 59
def prefixEnd_3616727 : Nat := 4983230072969 + 3 ^ 40 * 3616727 * 2
def baseEnd_3616727 : Nat := 1857119347093776272679481

theorem tailTrace_3616727 : CollatzResearch.WordTrace tailWord_3616727 prefixEnd_3616727 1857119347093776272679481 := by
  unfold tailWord_3616727
  simp only [CollatzResearch.WordTrace]
  refine ⟨131912870768223241640072435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87941913845482161093381623 131912870768223241640072435)
  ·
    refine ⟨197869306152334862460108653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131912870768223241640072435 197869306152334862460108653)
    ·
      refine ⟨74200989807125573422540745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197869306152334862460108653 74200989807125573422540745)
      ·
        refine ⟨55650742355344180066905559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74200989807125573422540745 55650742355344180066905559)
        ·
          refine ⟨83476113533016270100358339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55650742355344180066905559 83476113533016270100358339)
          ·
            refine ⟨125214170299524405150537509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83476113533016270100358339 125214170299524405150537509)
            ·
              refine ⟨23477656931160825965725783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125214170299524405150537509 23477656931160825965725783)
              ·
                refine ⟨35216485396741238948588675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23477656931160825965725783 35216485396741238948588675)
                ·
                  refine ⟨52824728095111858422883013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35216485396741238948588675 52824728095111858422883013)
                  ·
                    refine ⟨9904636517833473454290565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52824728095111858422883013 9904636517833473454290565)
                    ·
                      refine ⟨1857119347093776272679481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9904636517833473454290565 1857119347093776272679481)
                      ·
                        rfl

theorem cell23_3616727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3616727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616727 prefixEnd_3616727 := by exact prefixLift 3616727
  have htrace : WordTrace (prefixWord ++ tailWord_3616727) baseStart_3616727 baseEnd_3616727 := by
    simpa [prefixWord, tailWord_3616727, baseEnd_3616727] using wordTrace_append hprefix tailTrace_3616727
  have hstable : (prefixWord ++ tailWord_3616727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616727).length < 2 ^ (prefixWord ++ tailWord_3616727).sum := by decide
  have hdescent : baseEnd_3616727 < baseStart_3616727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616737 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 7]
def baseStart_3616737 : Nat := 118140960795 + 3616737 * 2 ^ 59
def prefixEnd_3616737 : Nat := 4983230072969 + 3 ^ 40 * 3616737 * 2
def baseEnd_3616737 : Nat := 206347164655591248172715

theorem tailTrace_3616737 : CollatzResearch.WordTrace tailWord_3616737 prefixEnd_3616737 206347164655591248172715 := by
  unfold tailWord_3616737
  simp only [CollatzResearch.WordTrace]
  refine ⟨131913235498187013347936465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87942156998791342231957643 131913235498187013347936465)
  ·
    refine ⟨98934926623640260010952349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131913235498187013347936465 98934926623640260010952349)
    ·
      refine ⟨37100597483865097504107131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98934926623640260010952349 37100597483865097504107131)
      ·
        refine ⟨55650896225797646256160697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37100597483865097504107131 55650896225797646256160697)
        ·
          refine ⟨41738172169348234692120523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55650896225797646256160697 41738172169348234692120523)
          ·
            refine ⟨62607258254022352038180785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41738172169348234692120523 62607258254022352038180785)
            ·
              refine ⟨46955443690516764028635589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62607258254022352038180785 46955443690516764028635589)
              ·
                refine ⟨8804145691971893255369173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46955443690516764028635589 8804145691971893255369173)
                ·
                  refine ⟨206347164655591248172715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8804145691971893255369173 206347164655591248172715)
                  ·
                    rfl

theorem cell23_3616737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_3616737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616737 prefixEnd_3616737 := by exact prefixLift 3616737
  have htrace : WordTrace (prefixWord ++ tailWord_3616737) baseStart_3616737 baseEnd_3616737 := by
    simpa [prefixWord, tailWord_3616737, baseEnd_3616737] using wordTrace_append hprefix tailTrace_3616737
  have hstable : (prefixWord ++ tailWord_3616737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616737).length < 2 ^ (prefixWord ++ tailWord_3616737).sum := by decide
  have hdescent : baseEnd_3616737 < baseStart_3616737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616764 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3616764 : Nat := 118140960795 + 3616764 * 2 ^ 59
def prefixEnd_3616764 : Nat := 4983230072969 + 3 ^ 40 * 3616764 * 2
def baseEnd_3616764 : Nat := 1857138345877992627916811

theorem tailTrace_3616764 : CollatzResearch.WordTrace tailWord_3616764 prefixEnd_3616764 1857138345877992627916811 := by
  unfold tailWord_3616764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65957110134544598479584673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87942813512726131306112897 65957110134544598479584673)
  ·
    refine ⟨49467832600908448859688505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65957110134544598479584673 49467832600908448859688505)
    ·
      refine ⟨37100874450681336644766379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49467832600908448859688505 37100874450681336644766379)
      ·
        refine ⟨55651311676022004967149569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37100874450681336644766379 55651311676022004967149569)
        ·
          refine ⟨41738483757016503725362177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55651311676022004967149569 41738483757016503725362177)
          ·
            refine ⟨31303862817762377794021633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41738483757016503725362177 31303862817762377794021633)
            ·
              refine ⟨23477897113321783345516225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31303862817762377794021633 23477897113321783345516225)
              ·
                refine ⟨17608422834991337509137169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23477897113321783345516225 17608422834991337509137169)
                ·
                  refine ⟨13206317126243503131852877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17608422834991337509137169 13206317126243503131852877)
                  ·
                    refine ⟨4952368922341313674444829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13206317126243503131852877 4952368922341313674444829)
                    ·
                      refine ⟨1857138345877992627916811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952368922341313674444829 1857138345877992627916811)
                      ·
                        rfl

theorem cell23_3616764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3616764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616764 prefixEnd_3616764 := by exact prefixLift 3616764
  have htrace : WordTrace (prefixWord ++ tailWord_3616764) baseStart_3616764 baseEnd_3616764 := by
    simpa [prefixWord, tailWord_3616764, baseEnd_3616764] using wordTrace_append hprefix tailTrace_3616764
  have hstable : (prefixWord ++ tailWord_3616764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616764).length < 2 ^ (prefixWord ++ tailWord_3616764).sum := by decide
  have hdescent : baseEnd_3616764 < baseStart_3616764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616788 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3616788 : Nat := 118140960795 + 3616788 * 2 ^ 59
def prefixEnd_3616788 : Nat := 4983230072969 + 3 ^ 40 * 3616788 * 2
def baseEnd_3616788 : Nat := 206350074379300059335189

theorem tailTrace_3616788 : CollatzResearch.WordTrace tailWord_3616788 prefixEnd_3616788 206350074379300059335189 := by
  unfold tailWord_3616788
  simp only [CollatzResearch.WordTrace]
  refine ⟨65957547810501124529021509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87943397080668166038695345 65957547810501124529021509)
  ·
    refine ⟨12367040214468960849191533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65957547810501124529021509 12367040214468960849191533)
    ·
      refine ⟨4637640080425860318446825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12367040214468960849191533 4637640080425860318446825)
      ·
        refine ⟨3478230060319395238835119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637640080425860318446825 3478230060319395238835119)
        ·
          refine ⟨5217345090479092858252679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478230060319395238835119 5217345090479092858252679)
          ·
            refine ⟨7826017635718639287379019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217345090479092858252679 7826017635718639287379019)
            ·
              refine ⟨11739026453577958931068529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826017635718639287379019 11739026453577958931068529)
              ·
                refine ⟨8804269840183469198301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11739026453577958931068529 8804269840183469198301397)
                ·
                  refine ⟨206350074379300059335189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8804269840183469198301397 206350074379300059335189)
                  ·
                    rfl

theorem cell23_3616788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3616788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616788 prefixEnd_3616788 := by exact prefixLift 3616788
  have htrace : WordTrace (prefixWord ++ tailWord_3616788) baseStart_3616788 baseEnd_3616788 := by
    simpa [prefixWord, tailWord_3616788, baseEnd_3616788] using wordTrace_append hprefix tailTrace_3616788
  have hstable : (prefixWord ++ tailWord_3616788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616788).length < 2 ^ (prefixWord ++ tailWord_3616788).sum := by decide
  have hdescent : baseEnd_3616788 < baseStart_3616788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616821 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_3616821 : Nat := 118140960795 + 3616821 * 2 ^ 59
def prefixEnd_3616821 : Nat := 4983230072969 + 3 ^ 40 * 3616821 * 2
def baseEnd_3616821 : Nat := 1857167614275298904904049

theorem tailTrace_3616821 : CollatzResearch.WordTrace tailWord_3616821 prefixEnd_3616821 1857167614275298904904049 := by
  unfold tailWord_3616821
  simp only [CollatzResearch.WordTrace]
  refine ⟨131916299229882695693994317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87944199486588463795996211 131916299229882695693994317)
  ·
    refine ⟨49468612211206010885247869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131916299229882695693994317 49468612211206010885247869)
    ·
      refine ⟨18550729579202254081967951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49468612211206010885247869 18550729579202254081967951)
      ·
        refine ⟨27826094368803381122951927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18550729579202254081967951 27826094368803381122951927)
        ·
          refine ⟨41739141553205071684427891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27826094368803381122951927 41739141553205071684427891)
          ·
            refine ⟨62608712329807607526641837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41739141553205071684427891 62608712329807607526641837)
            ·
              refine ⟨23478267123677852822490689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62608712329807607526641837 23478267123677852822490689)
              ·
                refine ⟨17608700342758389616868017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23478267123677852822490689 17608700342758389616868017)
                ·
                  refine ⟨13206525257068792212651013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17608700342758389616868017 13206525257068792212651013)
                  ·
                    refine ⟨2476223485700398539872065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13206525257068792212651013 2476223485700398539872065)
                    ·
                      refine ⟨1857167614275298904904049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476223485700398539872065 1857167614275298904904049)
                      ·
                        rfl

theorem cell23_3616821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_3616821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616821 prefixEnd_3616821 := by exact prefixLift 3616821
  have htrace : WordTrace (prefixWord ++ tailWord_3616821) baseStart_3616821 baseEnd_3616821 := by
    simpa [prefixWord, tailWord_3616821, baseEnd_3616821] using wordTrace_append hprefix tailTrace_3616821
  have hstable : (prefixWord ++ tailWord_3616821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616821).length < 2 ^ (prefixWord ++ tailWord_3616821).sum := by decide
  have hdescent : baseEnd_3616821 < baseStart_3616821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616827 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 8]
def baseStart_3616827 : Nat := 118140960795 + 3616827 * 2 ^ 59
def prefixEnd_3616827 : Nat := 4983230072969 + 3 ^ 40 * 3616827 * 2
def baseEnd_3616827 : Nat := 206352299462136209047669

theorem tailTrace_3616827 : CollatzResearch.WordTrace tailWord_3616827 prefixEnd_3616827 206352299462136209047669 := by
  unfold tailWord_3616827
  simp only [CollatzResearch.WordTrace]
  refine ⟨131916518067860958718712735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87944345378573972479141823 131916518067860958718712735)
  ·
    refine ⟨197874777101791438078069103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131916518067860958718712735 197874777101791438078069103)
    ·
      refine ⟨296812165652687157117103655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197874777101791438078069103 296812165652687157117103655)
      ·
        refine ⟨445218248479030735675655483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296812165652687157117103655 445218248479030735675655483)
        ·
          refine ⟨667827372718546103513483225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445218248479030735675655483 667827372718546103513483225)
          ·
            refine ⟨500870529538909577635112419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667827372718546103513483225 500870529538909577635112419)
            ·
              refine ⟨751305794308364366452668629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500870529538909577635112419 751305794308364366452668629)
              ·
                refine ⟨17608729554102289838734421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 751305794308364366452668629 17608729554102289838734421)
                ·
                  refine ⟨206352299462136209047669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17608729554102289838734421 206352299462136209047669)
                  ·
                    rfl

theorem cell23_3616827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_3616827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616827 prefixEnd_3616827 := by exact prefixLift 3616827
  have htrace : WordTrace (prefixWord ++ tailWord_3616827) baseStart_3616827 baseEnd_3616827 := by
    simpa [prefixWord, tailWord_3616827, baseEnd_3616827] using wordTrace_append hprefix tailTrace_3616827
  have hstable : (prefixWord ++ tailWord_3616827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616827).length < 2 ^ (prefixWord ++ tailWord_3616827).sum := by decide
  have hdescent : baseEnd_3616827 < baseStart_3616827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616844 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 6]
def baseStart_3616844 : Nat := 118140960795 + 3616844 * 2 ^ 59
def prefixEnd_3616844 : Nat := 4983230072969 + 3 ^ 40 * 3616844 * 2
def baseEnd_3616844 : Nat := 206353269370039146101827

theorem tailTrace_3616844 : CollatzResearch.WordTrace tailWord_3616844 prefixEnd_3616844 206353269370039146101827 := by
  unfold tailWord_3616844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65958569054399685311040793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87944758739199580414721057 65958569054399685311040793)
  ·
    refine ⟨49468926790799763983280595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65958569054399685311040793 49468926790799763983280595)
    ·
      refine ⟨74203390186199645974920893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49468926790799763983280595 74203390186199645974920893)
      ·
        refine ⟨27826271319824867240595335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74203390186199645974920893 27826271319824867240595335)
        ·
          refine ⟨41739406979737300860893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27826271319824867240595335 41739406979737300860893003)
          ·
            refine ⟨62609110469605951291339505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41739406979737300860893003 62609110469605951291339505)
            ·
              refine ⟨46956832852204463468504629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62609110469605951291339505 46956832852204463468504629)
              ·
                refine ⟨4402203079894168450172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46956832852204463468504629 4402203079894168450172309)
                ·
                  refine ⟨206353269370039146101827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4402203079894168450172309 206353269370039146101827)
                  ·
                    rfl

theorem cell23_3616844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_3616844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616844 prefixEnd_3616844 := by exact prefixLift 3616844
  have htrace : WordTrace (prefixWord ++ tailWord_3616844) baseStart_3616844 baseEnd_3616844 := by
    simpa [prefixWord, tailWord_3616844, baseEnd_3616844] using wordTrace_append hprefix tailTrace_3616844
  have hstable : (prefixWord ++ tailWord_3616844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616844).length < 2 ^ (prefixWord ++ tailWord_3616844).sum := by decide
  have hdescent : baseEnd_3616844 < baseStart_3616844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616861 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 8]
def baseStart_3616861 : Nat := 118140960795 + 3616861 * 2 ^ 59
def prefixEnd_3616861 : Nat := 4983230072969 + 3 ^ 40 * 3616861 * 2
def baseEnd_3616861 : Nat := 206354239277942083155985

theorem tailTrace_3616861 : CollatzResearch.WordTrace tailWord_3616861 prefixEnd_3616861 206354239277942083155985 := by
  unfold tailWord_3616861
  simp only [CollatzResearch.WordTrace]
  refine ⟨131917758149737782525450437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87945172099825188350300291 131917758149737782525450437)
  ·
    refine ⟨24734579653075834223521957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131917758149737782525450437 24734579653075834223521957)
    ·
      refine ⟨4637733684951718916910367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24734579653075834223521957 4637733684951718916910367)
      ·
        refine ⟨6956600527427578375365551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637733684951718916910367 6956600527427578375365551)
        ·
          refine ⟨10434900791141367563048327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956600527427578375365551 10434900791141367563048327)
          ·
            refine ⟨15652351186712051344572491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434900791141367563048327 15652351186712051344572491)
            ·
              refine ⟨23478526780068077016858737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15652351186712051344572491 23478526780068077016858737)
              ·
                refine ⟨17608895085051057762644053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23478526780068077016858737 17608895085051057762644053)
                ·
                  refine ⟨206354239277942083155985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17608895085051057762644053 206354239277942083155985)
                  ·
                    rfl

theorem cell23_3616861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_3616861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616861 prefixEnd_3616861 := by exact prefixLift 3616861
  have htrace : WordTrace (prefixWord ++ tailWord_3616861) baseStart_3616861 baseEnd_3616861 := by
    simpa [prefixWord, tailWord_3616861, baseEnd_3616861] using wordTrace_append hprefix tailTrace_3616861
  have hstable : (prefixWord ++ tailWord_3616861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616861).length < 2 ^ (prefixWord ++ tailWord_3616861).sum := by decide
  have hdescent : baseEnd_3616861 < baseStart_3616861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616951 : List Nat := [1, 1, 3, 1, 4, 4, 1, 8]
def baseStart_3616951 : Nat := 118140960795 + 3616951 * 2 ^ 59
def prefixEnd_3616951 : Nat := 4983230072969 + 3 ^ 40 * 3616951 * 2
def baseEnd_3616951 : Nat := 68786458028162348010313

theorem tailTrace_3616951 : CollatzResearch.WordTrace tailWord_3616951 prefixEnd_3616951 68786458028162348010313 := by
  unfold tailWord_3616951
  simp only [CollatzResearch.WordTrace]
  refine ⟨131921040719411727896226707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87947360479607818597484471 131921040719411727896226707)
  ·
    refine ⟨197881561079117591844340061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131921040719411727896226707 197881561079117591844340061)
    ·
      refine ⟨74205585404669096941627523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197881561079117591844340061 74205585404669096941627523)
      ·
        refine ⟨111308378107003645412441285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74205585404669096941627523 111308378107003645412441285)
        ·
          refine ⟨20870320895063183514832741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111308378107003645412441285 20870320895063183514832741)
          ·
            refine ⟨3913185167824346909031139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20870320895063183514832741 3913185167824346909031139)
            ·
              refine ⟨5869777751736520363546709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913185167824346909031139 5869777751736520363546709)
              ·
                refine ⟨68786458028162348010313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5869777751736520363546709 68786458028162348010313)
                ·
                  rfl

theorem cell23_3616951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 8].length) (baseStart_3616951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616951 prefixEnd_3616951 := by exact prefixLift 3616951
  have htrace : WordTrace (prefixWord ++ tailWord_3616951) baseStart_3616951 baseEnd_3616951 := by
    simpa [prefixWord, tailWord_3616951, baseEnd_3616951] using wordTrace_append hprefix tailTrace_3616951
  have hstable : (prefixWord ++ tailWord_3616951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616951).length < 2 ^ (prefixWord ++ tailWord_3616951).sum := by decide
  have hdescent : baseEnd_3616951 < baseStart_3616951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616954 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_3616954 : Nat := 118140960795 + 3616954 * 2 ^ 59
def prefixEnd_3616954 : Nat := 4983230072969 + 3 ^ 40 * 3616954 * 2
def baseEnd_3616954 : Nat := 1857235907202346884540937

theorem tailTrace_3616954 : CollatzResearch.WordTrace tailWord_3616954 prefixEnd_3616954 1857235907202346884540937 := by
  unfold tailWord_3616954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980287534600214852146479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87947433425600572939057277 32980287534600214852146479)
  ·
    refine ⟨49470431301900322278219719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32980287534600214852146479 49470431301900322278219719)
    ·
      refine ⟨74205646952850483417329579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49470431301900322278219719 74205646952850483417329579)
      ·
        refine ⟨111308470429275725125994369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74205646952850483417329579 111308470429275725125994369)
        ·
          refine ⟨83481352821956793844495777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111308470429275725125994369 83481352821956793844495777)
          ·
            refine ⟨62611014616467595383371833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83481352821956793844495777 62611014616467595383371833)
            ·
              refine ⟨46958260962350696537528875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62611014616467595383371833 46958260962350696537528875)
              ·
                refine ⟨70437391443526044806293313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46958260962350696537528875 70437391443526044806293313)
                ·
                  refine ⟨52828043582644533604719985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70437391443526044806293313 52828043582644533604719985)
                  ·
                    refine ⟨39621032686983400203539989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52828043582644533604719985 39621032686983400203539989)
                    ·
                      refine ⟨1857235907202346884540937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39621032686983400203539989 1857235907202346884540937)
                      ·
                        rfl

theorem cell23_3616954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_3616954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616954 prefixEnd_3616954 := by exact prefixLift 3616954
  have htrace : WordTrace (prefixWord ++ tailWord_3616954) baseStart_3616954 baseEnd_3616954 := by
    simpa [prefixWord, tailWord_3616954, baseEnd_3616954] using wordTrace_append hprefix tailTrace_3616954
  have hstable : (prefixWord ++ tailWord_3616954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616954).length < 2 ^ (prefixWord ++ tailWord_3616954).sum := by decide
  have hdescent : baseEnd_3616954 < baseStart_3616954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616978 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3616978 : Nat := 118140960795 + 3616978 * 2 ^ 59
def prefixEnd_3616978 : Nat := 4983230072969 + 3 ^ 40 * 3616978 * 2
def baseEnd_3616978 : Nat := 1857248230738054790640827

theorem tailTrace_3616978 : CollatzResearch.WordTrace tailWord_3616978 prefixEnd_3616978 1857248230738054790640827 := by
  unfold tailWord_3616978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980506372578477876864897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87948016993542607671639725 32980506372578477876864897)
  ·
    refine ⟨24735379779433858407648673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32980506372578477876864897 24735379779433858407648673)
    ·
      refine ⟨18551534834575393805736505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24735379779433858407648673 18551534834575393805736505)
      ·
        refine ⟨13913651125931545354302379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18551534834575393805736505 13913651125931545354302379)
        ·
          refine ⟨20870476688897318031453569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913651125931545354302379 20870476688897318031453569)
          ·
            refine ⟨15652857516672988523590177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20870476688897318031453569 15652857516672988523590177)
            ·
              refine ⟨11739643137504741392692633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15652857516672988523590177 11739643137504741392692633)
              ·
                refine ⟨8804732353128556044519475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11739643137504741392692633 8804732353128556044519475)
                ·
                  refine ⟨13207098529692834066779213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8804732353128556044519475 13207098529692834066779213)
                  ·
                    refine ⟨4952661948634812775042205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13207098529692834066779213 4952661948634812775042205)
                    ·
                      refine ⟨1857248230738054790640827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952661948634812775042205 1857248230738054790640827)
                      ·
                        rfl

theorem cell23_3616978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3616978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616978 prefixEnd_3616978 := by exact prefixLift 3616978
  have htrace : WordTrace (prefixWord ++ tailWord_3616978) baseStart_3616978 baseEnd_3616978 := by
    simpa [prefixWord, tailWord_3616978, baseEnd_3616978] using wordTrace_append hprefix tailTrace_3616978
  have hstable : (prefixWord ++ tailWord_3616978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616978).length < 2 ^ (prefixWord ++ tailWord_3616978).sum := by decide
  have hdescent : baseEnd_3616978 < baseStart_3616978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3616982 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3616982 : Nat := 118140960795 + 3616982 * 2 ^ 59
def prefixEnd_3616982 : Nat := 4983230072969 + 3 ^ 40 * 3616982 * 2
def baseEnd_3616982 : Nat := 1857250284660672774990809

theorem tailTrace_3616982 : CollatzResearch.WordTrace tailWord_3616982 prefixEnd_3616982 1857250284660672774990809 := by
  unfold tailWord_3616982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245135711393713761912825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87948114254866280127070133 8245135711393713761912825)
  ·
    refine ⟨6183851783545285321434619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8245135711393713761912825 6183851783545285321434619)
    ·
      refine ⟨9275777675317927982151929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183851783545285321434619 9275777675317927982151929)
      ·
        refine ⟨6956833256488445986613947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9275777675317927982151929 6956833256488445986613947)
        ·
          refine ⟨10435249884732668979920921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956833256488445986613947 10435249884732668979920921)
          ·
            refine ⟨7826437413549501734940691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435249884732668979920921 7826437413549501734940691)
            ·
              refine ⟨11739656120324252602411037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826437413549501734940691 11739656120324252602411037)
              ·
                refine ⟨4402371045121594725904139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11739656120324252602411037 4402371045121594725904139)
                ·
                  refine ⟨6603556567682392088856209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402371045121594725904139 6603556567682392088856209)
                  ·
                    refine ⟨4952667425761794066642157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6603556567682392088856209 4952667425761794066642157)
                    ·
                      refine ⟨1857250284660672774990809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952667425761794066642157 1857250284660672774990809)
                      ·
                        rfl

theorem cell23_3616982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3616982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3616982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3616982 prefixEnd_3616982 := by exact prefixLift 3616982
  have htrace : WordTrace (prefixWord ++ tailWord_3616982) baseStart_3616982 baseEnd_3616982 := by
    simpa [prefixWord, tailWord_3616982, baseEnd_3616982] using wordTrace_append hprefix tailTrace_3616982
  have hstable : (prefixWord ++ tailWord_3616982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3616982).length < 2 ^ (prefixWord ++ tailWord_3616982).sum := by decide
  have hdescent : baseEnd_3616982 < baseStart_3616982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3616982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617021 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_3617021 : Nat := 118140960795 + 3617021 * 2 ^ 59
def prefixEnd_3617021 : Nat := 4983230072969 + 3 ^ 40 * 3617021 * 2
def baseEnd_3617021 : Nat := 1857270310406198122403129

theorem tailTrace_3617021 : CollatzResearch.WordTrace tailWord_3617021 prefixEnd_3617021 1857270310406198122403129 := by
  unfold tailWord_3617021
  simp only [CollatzResearch.WordTrace]
  refine ⟨131923593829158129851274917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87949062552772086567516611 131923593829158129851274917)
  ·
    refine ⟨24735673842967149347114047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131923593829158129851274917 24735673842967149347114047)
    ·
      refine ⟨37103510764450724020671071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24735673842967149347114047 37103510764450724020671071)
      ·
        refine ⟨55655266146676086031006607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37103510764450724020671071 55655266146676086031006607)
        ·
          refine ⟨83482899220014129046509911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55655266146676086031006607 83482899220014129046509911)
          ·
            refine ⟨125224348830021193569764867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83482899220014129046509911 125224348830021193569764867)
            ·
              refine ⟨187836523245031790354647301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125224348830021193569764867 187836523245031790354647301)
              ·
                refine ⟨35219348108443460691496369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187836523245031790354647301 35219348108443460691496369)
                ·
                  refine ⟨26414511081332595518622277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35219348108443460691496369 26414511081332595518622277)
                  ·
                    refine ⟨4952720827749861659741677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26414511081332595518622277 4952720827749861659741677)
                    ·
                      refine ⟨1857270310406198122403129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952720827749861659741677 1857270310406198122403129)
                      ·
                        rfl

theorem cell23_3617021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_3617021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617021 prefixEnd_3617021 := by exact prefixLift 3617021
  have htrace : WordTrace (prefixWord ++ tailWord_3617021) baseStart_3617021 baseEnd_3617021 := by
    simpa [prefixWord, tailWord_3617021, baseEnd_3617021] using wordTrace_append hprefix tailTrace_3617021
  have hstable : (prefixWord ++ tailWord_3617021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617021).length < 2 ^ (prefixWord ++ tailWord_3617021).sum := by decide
  have hdescent : baseEnd_3617021 < baseStart_3617021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617022 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3617022 : Nat := 118140960795 + 3617022 * 2 ^ 59
def prefixEnd_3617022 : Nat := 4983230072969 + 3 ^ 40 * 3617022 * 2
def baseEnd_3617022 : Nat := 1857270823886852618490625

theorem tailTrace_3617022 : CollatzResearch.WordTrace tailWord_3617022 prefixEnd_3617022 1857270823886852618490625 := by
  unfold tailWord_3617022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16490453787769313377757665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87949086868103004681374213 16490453787769313377757665)
  ·
    refine ⟨12367840340826985033318249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16490453787769313377757665 12367840340826985033318249)
    ·
      refine ⟨9275880255620238774988687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12367840340826985033318249 9275880255620238774988687)
      ·
        refine ⟨13913820383430358162483031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275880255620238774988687 13913820383430358162483031)
        ·
          refine ⟨20870730575145537243724547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913820383430358162483031 20870730575145537243724547)
          ·
            refine ⟨31306095862718305865586821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870730575145537243724547 31306095862718305865586821)
            ·
              refine ⟨5869892974259682349797529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31306095862718305865586821 5869892974259682349797529)
              ·
                refine ⟨4402419730694761762348147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869892974259682349797529 4402419730694761762348147)
                ·
                  refine ⟨6603629596042142643522221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402419730694761762348147 6603629596042142643522221)
                  ·
                    refine ⟨2476361098515803491320833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6603629596042142643522221 2476361098515803491320833)
                    ·
                      refine ⟨1857270823886852618490625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476361098515803491320833 1857270823886852618490625)
                      ·
                        rfl

theorem cell23_3617022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3617022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617022 prefixEnd_3617022 := by exact prefixLift 3617022
  have htrace : WordTrace (prefixWord ++ tailWord_3617022) baseStart_3617022 baseEnd_3617022 := by
    simpa [prefixWord, tailWord_3617022, baseEnd_3617022] using wordTrace_append hprefix tailTrace_3617022
  have hstable : (prefixWord ++ tailWord_3617022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617022).length < 2 ^ (prefixWord ++ tailWord_3617022).sum := by decide
  have hdescent : baseEnd_3617022 < baseStart_3617022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617051 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3]
def baseStart_3617051 : Nat := 118140960795 + 3617051 * 2 ^ 59
def prefixEnd_3617051 : Nat := 4983230072969 + 3 ^ 40 * 3617051 * 2
def baseEnd_3617051 : Nat := 1857285714825833005027991

theorem tailTrace_3617051 : CollatzResearch.WordTrace tailWord_3617051 prefixEnd_3617051 1857285714825833005027991 := by
  unfold tailWord_3617051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131924688019049444974867007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87949792012699629983244671 131924688019049444974867007)
  ·
    refine ⟨197887032028574167462300511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131924688019049444974867007 197887032028574167462300511)
    ·
      refine ⟨296830548042861251193450767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197887032028574167462300511 296830548042861251193450767)
      ·
        refine ⟨445245822064291876790176151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296830548042861251193450767 445245822064291876790176151)
        ·
          refine ⟨667868733096437815185264227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445245822064291876790176151 667868733096437815185264227)
          ·
            refine ⟨1001803099644656722777896341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667868733096437815185264227 1001803099644656722777896341)
            ·
              refine ⟨46959520295843283880213891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1001803099644656722777896341 46959520295843283880213891)
              ·
                refine ⟨70439280443764925820320837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46959520295843283880213891 70439280443764925820320837)
                ·
                  refine ⟨13207365083205923591310157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70439280443764925820320837 13207365083205923591310157)
                  ·
                    refine ⟨4952761906202221346741309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13207365083205923591310157 4952761906202221346741309)
                    ·
                      refine ⟨1857285714825833005027991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952761906202221346741309 1857285714825833005027991)
                      ·
                        rfl

theorem cell23_3617051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].length) (baseStart_3617051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617051 prefixEnd_3617051 := by exact prefixLift 3617051
  have htrace : WordTrace (prefixWord ++ tailWord_3617051) baseStart_3617051 baseEnd_3617051 := by
    simpa [prefixWord, tailWord_3617051, baseEnd_3617051] using wordTrace_append hprefix tailTrace_3617051
  have hstable : (prefixWord ++ tailWord_3617051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617051).length < 2 ^ (prefixWord ++ tailWord_3617051).sum := by decide
  have hdescent : baseEnd_3617051 < baseStart_3617051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617058 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3617058 : Nat := 118140960795 + 3617058 * 2 ^ 59
def prefixEnd_3617058 : Nat := 4983230072969 + 3 ^ 40 * 3617058 * 2
def baseEnd_3617058 : Nat := 206365478798934941960051

theorem tailTrace_3617058 : CollatzResearch.WordTrace tailWord_3617058 prefixEnd_3617058 206365478798934941960051 := by
  unfold tailWord_3617058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981235832506021292592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87949962220016056780247885 32981235832506021292592957)
  ·
    refine ⟨12367963437189757984722359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32981235832506021292592957 12367963437189757984722359)
    ·
      refine ⟨18551945155784636977083539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367963437189757984722359 18551945155784636977083539)
      ·
        refine ⟨27827917733676955465625309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551945155784636977083539 27827917733676955465625309)
        ·
          refine ⟨10435469150128858299609491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27827917733676955465625309 10435469150128858299609491)
          ·
            refine ⟨15653203725193287449414237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435469150128858299609491 15653203725193287449414237)
            ·
              refine ⟨5869951396947482793530339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15653203725193287449414237 5869951396947482793530339)
              ·
                refine ⟨8804927095421224190295509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869951396947482793530339 8804927095421224190295509)
                ·
                  refine ⟨206365478798934941960051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8804927095421224190295509 206365478798934941960051)
                  ·
                    rfl

theorem cell23_3617058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3617058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617058 prefixEnd_3617058 := by exact prefixLift 3617058
  have htrace : WordTrace (prefixWord ++ tailWord_3617058) baseStart_3617058 baseEnd_3617058 := by
    simpa [prefixWord, tailWord_3617058, baseEnd_3617058] using wordTrace_append hprefix tailTrace_3617058
  have hstable : (prefixWord ++ tailWord_3617058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617058).length < 2 ^ (prefixWord ++ tailWord_3617058).sum := by decide
  have hdescent : baseEnd_3617058 < baseStart_3617058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617063 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3617063 : Nat := 118140960795 + 3617063 * 2 ^ 59
def prefixEnd_3617063 : Nat := 4983230072969 + 3 ^ 40 * 3617063 * 2
def baseEnd_3617063 : Nat := 1857291876593686958077937

theorem tailTrace_3617063 : CollatzResearch.WordTrace tailWord_3617063 prefixEnd_3617063 1857291876593686958077937 := by
  unfold tailWord_3617063
  simp only [CollatzResearch.WordTrace]
  refine ⟨131925125695005971024303843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87950083796670647349535895 131925125695005971024303843)
  ·
    refine ⟨197887688542508956536455765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131925125695005971024303843 197887688542508956536455765)
    ·
      refine ⟨2318996350107526834411591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 197887688542508956536455765 2318996350107526834411591)
      ·
        refine ⟨3478494525161290251617387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318996350107526834411591 3478494525161290251617387)
        ·
          refine ⟨5217741787741935377426081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478494525161290251617387 5217741787741935377426081)
          ·
            refine ⟨3913306340806451533069561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217741787741935377426081 3913306340806451533069561)
            ·
              refine ⟨2934979755604838649802171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913306340806451533069561 2934979755604838649802171)
              ·
                refine ⟨4402469633407257974703257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934979755604838649802171 4402469633407257974703257)
                ·
                  refine ⟨3301852225055443481027443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402469633407257974703257 3301852225055443481027443)
                  ·
                    refine ⟨4952778337583165221541165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301852225055443481027443 4952778337583165221541165)
                    ·
                      refine ⟨1857291876593686958077937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952778337583165221541165 1857291876593686958077937)
                      ·
                        rfl

theorem cell23_3617063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3617063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617063 prefixEnd_3617063 := by exact prefixLift 3617063
  have htrace : WordTrace (prefixWord ++ tailWord_3617063) baseStart_3617063 baseEnd_3617063 := by
    simpa [prefixWord, tailWord_3617063, baseEnd_3617063] using wordTrace_append hprefix tailTrace_3617063
  have hstable : (prefixWord ++ tailWord_3617063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617063).length < 2 ^ (prefixWord ++ tailWord_3617063).sum := by decide
  have hdescent : baseEnd_3617063 < baseStart_3617063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617091 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3617091 : Nat := 118140960795 + 3617091 * 2 ^ 59
def prefixEnd_3617091 : Nat := 4983230072969 + 3 ^ 40 * 3617091 * 2
def baseEnd_3617091 : Nat := 1857306254052012848527807

theorem tailTrace_3617091 : CollatzResearch.WordTrace tailWord_3617091 prefixEnd_3617091 1857306254052012848527807 := by
  unfold tailWord_3617091
  simp only [CollatzResearch.WordTrace]
  refine ⟨131926146938904531806323127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87950764625936354537548751 131926146938904531806323127)
  ·
    refine ⟨197889220408356797709484691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131926146938904531806323127 197889220408356797709484691)
    ·
      refine ⟨296833830612535196564227037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197889220408356797709484691 296833830612535196564227037)
      ·
        refine ⟨111312686479700698711585139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296833830612535196564227037 111312686479700698711585139)
        ·
          refine ⟨166969029719551048067377709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111312686479700698711585139 166969029719551048067377709)
          ·
            refine ⟨62613386144831643025266641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166969029719551048067377709 62613386144831643025266641)
            ·
              refine ⟨46960039608623732268949981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62613386144831643025266641 46960039608623732268949981)
              ·
                refine ⟨17610014853233899600856243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46960039608623732268949981 17610014853233899600856243)
                ·
                  refine ⟨26415022279850849401284365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17610014853233899600856243 26415022279850849401284365)
                  ·
                    refine ⟨9905633354944068525481637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26415022279850849401284365 9905633354944068525481637)
                    ·
                      refine ⟨1857306254052012848527807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9905633354944068525481637 1857306254052012848527807)
                      ·
                        rfl

theorem cell23_3617091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3617091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617091 prefixEnd_3617091 := by exact prefixLift 3617091
  have htrace : WordTrace (prefixWord ++ tailWord_3617091) baseStart_3617091 baseEnd_3617091 := by
    simpa [prefixWord, tailWord_3617091, baseEnd_3617091] using wordTrace_append hprefix tailTrace_3617091
  have hstable : (prefixWord ++ tailWord_3617091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617091).length < 2 ^ (prefixWord ++ tailWord_3617091).sum := by decide
  have hdescent : baseEnd_3617091 < baseStart_3617091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617109 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 5]
def baseStart_3617109 : Nat := 118140960795 + 3617109 * 2 ^ 59
def prefixEnd_3617109 : Nat := 4983230072969 + 3 ^ 40 * 3617109 * 2
def baseEnd_3617109 : Nat := 206368388522643753122525

theorem tailTrace_3617109 : CollatzResearch.WordTrace tailWord_3617109 prefixEnd_3617109 206368388522643753122525 := by
  unfold tailWord_3617109
  simp only [CollatzResearch.WordTrace]
  refine ⟨131926803452839320880478381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87951202301892880586985587 131926803452839320880478381)
  ·
    refine ⟨49472551294814745330179393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131926803452839320880478381 49472551294814745330179393)
    ·
      refine ⟨37104413471111058997634545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49472551294814745330179393 37104413471111058997634545)
      ·
        refine ⟨27828310103333294248225909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37104413471111058997634545 27828310103333294248225909)
        ·
          refine ⟨2608904072187496335771179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27828310103333294248225909 2608904072187496335771179)
          ·
            refine ⟨3913356108281244503656769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608904072187496335771179 3913356108281244503656769)
            ·
              refine ⟨2935017081210933377742577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913356108281244503656769 2935017081210933377742577)
              ·
                refine ⟨2201262810908200033306933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935017081210933377742577 2201262810908200033306933)
                ·
                  refine ⟨206368388522643753122525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201262810908200033306933 206368388522643753122525)
                  ·
                    rfl

theorem cell23_3617109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_3617109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617109 prefixEnd_3617109 := by exact prefixLift 3617109
  have htrace : WordTrace (prefixWord ++ tailWord_3617109) baseStart_3617109 baseEnd_3617109 := by
    simpa [prefixWord, tailWord_3617109, baseEnd_3617109] using wordTrace_append hprefix tailTrace_3617109
  have hstable : (prefixWord ++ tailWord_3617109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617109).length < 2 ^ (prefixWord ++ tailWord_3617109).sum := by decide
  have hdescent : baseEnd_3617109 < baseStart_3617109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617111 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3617111 : Nat := 118140960795 + 3617111 * 2 ^ 59
def prefixEnd_3617111 : Nat := 4983230072969 + 3 ^ 40 * 3617111 * 2
def baseEnd_3617111 : Nat := 1857316523665102770277715

theorem tailTrace_3617111 : CollatzResearch.WordTrace tailWord_3617111 prefixEnd_3617111 1857316523665102770277715 := by
  unfold tailWord_3617111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131926876398832075222051187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87951250932554716814700791 131926876398832075222051187)
  ·
    refine ⟨197890314598248112833076781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131926876398832075222051187 197890314598248112833076781)
    ·
      refine ⟨74208867974343042312403793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197890314598248112833076781 74208867974343042312403793)
      ·
        refine ⟨55656650980757281734302845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74208867974343042312403793 55656650980757281734302845)
        ·
          refine ⟨20871244117783980650363567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55656650980757281734302845 20871244117783980650363567)
          ·
            refine ⟨31306866176675970975545351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20871244117783980650363567 31306866176675970975545351)
            ·
              refine ⟨46960299265013956463318027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31306866176675970975545351 46960299265013956463318027)
              ·
                refine ⟨70440448897520934694977041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46960299265013956463318027 70440448897520934694977041)
                ·
                  refine ⟨52830336673140701021232781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70440448897520934694977041 52830336673140701021232781)
                  ·
                    refine ⟨19811376252427762882962293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52830336673140701021232781 19811376252427762882962293)
                    ·
                      refine ⟨1857316523665102770277715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19811376252427762882962293 1857316523665102770277715)
                      ·
                        rfl

theorem cell23_3617111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3617111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617111 prefixEnd_3617111 := by exact prefixLift 3617111
  have htrace : WordTrace (prefixWord ++ tailWord_3617111) baseStart_3617111 baseEnd_3617111 := by
    simpa [prefixWord, tailWord_3617111, baseEnd_3617111] using wordTrace_append hprefix tailTrace_3617111
  have hstable : (prefixWord ++ tailWord_3617111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617111).length < 2 ^ (prefixWord ++ tailWord_3617111).sum := by decide
  have hdescent : baseEnd_3617111 < baseStart_3617111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617121 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3617121 : Nat := 118140960795 + 3617121 * 2 ^ 59
def prefixEnd_3617121 : Nat := 4983230072969 + 3 ^ 40 * 3617121 * 2
def baseEnd_3617121 : Nat := 1857321658471647731152669

theorem tailTrace_3617121 : CollatzResearch.WordTrace tailWord_3617121 prefixEnd_3617121 1857321658471647731152669 := by
  unfold tailWord_3617121
  simp only [CollatzResearch.WordTrace]
  refine ⟨131927241128795846929915217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87951494085863897953276811 131927241128795846929915217)
  ·
    refine ⟨98945430846596885197436413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131927241128795846929915217 98945430846596885197436413)
    ·
      refine ⟨37104536567473831949038655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98945430846596885197436413 37104536567473831949038655)
      ·
        refine ⟨55656804851210747923557983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37104536567473831949038655 55656804851210747923557983)
        ·
          refine ⟨83485207276816121885336975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55656804851210747923557983 83485207276816121885336975)
          ·
            refine ⟨125227810915224182828005463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83485207276816121885336975 125227810915224182828005463)
            ·
              refine ⟨187841716372836274242008195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125227810915224182828005463 187841716372836274242008195)
              ·
                refine ⟨281762574559254411363012293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187841716372836274242008195 281762574559254411363012293)
                ·
                  refine ⟨52830482729860202130564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281762574559254411363012293 52830482729860202130564805)
                  ·
                    refine ⟨9905715511848787899480901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52830482729860202130564805 9905715511848787899480901)
                    ·
                      refine ⟨1857321658471647731152669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9905715511848787899480901 1857321658471647731152669)
                      ·
                        rfl

theorem cell23_3617121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3617121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617121 prefixEnd_3617121 := by exact prefixLift 3617121
  have htrace : WordTrace (prefixWord ++ tailWord_3617121) baseStart_3617121 baseEnd_3617121 := by
    simpa [prefixWord, tailWord_3617121, baseEnd_3617121] using wordTrace_append hprefix tailTrace_3617121
  have hstable : (prefixWord ++ tailWord_3617121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617121).length < 2 ^ (prefixWord ++ tailWord_3617121).sum := by decide
  have hdescent : baseEnd_3617121 < baseStart_3617121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617125 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_3617125 : Nat := 118140960795 + 3617125 * 2 ^ 59
def prefixEnd_3617125 : Nat := 4983230072969 + 3 ^ 40 * 3617125 * 2
def baseEnd_3617125 : Nat := 1857323712394265715502651

theorem tailTrace_3617125 : CollatzResearch.WordTrace tailWord_3617125 prefixEnd_3617125 1857323712394265715502651 := by
  unfold tailWord_3617125
  simp only [CollatzResearch.WordTrace]
  refine ⟨131927387020781355613060829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87951591347187570408707219 131927387020781355613060829)
  ·
    refine ⟨49472770132793008354897811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131927387020781355613060829 49472770132793008354897811)
    ·
      refine ⟨74209155199189512532346717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49472770132793008354897811 74209155199189512532346717)
      ·
        refine ⟨27828433199696067199630019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74209155199189512532346717 27828433199696067199630019)
        ·
          refine ⟨41742649799544100799445029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27828433199696067199630019 41742649799544100799445029)
          ·
            refine ⟨7826746837414518899895943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41742649799544100799445029 7826746837414518899895943)
            ·
              refine ⟨11740120256121778349843915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826746837414518899895943 11740120256121778349843915)
              ·
                refine ⟨17610180384182667524765873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740120256121778349843915 17610180384182667524765873)
                ·
                  refine ⟨13207635288137000643574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17610180384182667524765873 13207635288137000643574405)
                  ·
                    refine ⟨2476431616525687620670201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13207635288137000643574405 2476431616525687620670201)
                    ·
                      refine ⟨1857323712394265715502651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476431616525687620670201 1857323712394265715502651)
                      ·
                        rfl

theorem cell23_3617125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_3617125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617125 prefixEnd_3617125 := by exact prefixLift 3617125
  have htrace : WordTrace (prefixWord ++ tailWord_3617125) baseStart_3617125 baseEnd_3617125 := by
    simpa [prefixWord, tailWord_3617125, baseEnd_3617125] using wordTrace_append hprefix tailTrace_3617125
  have hstable : (prefixWord ++ tailWord_3617125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617125).length < 2 ^ (prefixWord ++ tailWord_3617125).sum := by decide
  have hdescent : baseEnd_3617125 < baseStart_3617125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617142 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3617142 : Nat := 118140960795 + 3617142 * 2 ^ 59
def prefixEnd_3617142 : Nat := 4983230072969 + 3 ^ 40 * 3617142 * 2
def baseEnd_3617142 : Nat := 1857332441565392148990073

theorem tailTrace_3617142 : CollatzResearch.WordTrace tailWord_3617142 prefixEnd_3617142 1857332441565392148990073 := by
  unfold tailWord_3617142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245500441357485469776855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87952004707813178344286453 8245500441357485469776855)
  ·
    refine ⟨12368250662036228204665283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245500441357485469776855 12368250662036228204665283)
    ·
      refine ⟨18552375993054342306997925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12368250662036228204665283 18552375993054342306997925)
      ·
        refine ⟨3478570498697689182562111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18552375993054342306997925 3478570498697689182562111)
        ·
          refine ⟨5217855748046533773843167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478570498697689182562111 5217855748046533773843167)
          ·
            refine ⟨7826783622069800660764751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217855748046533773843167 7826783622069800660764751)
            ·
              refine ⟨11740175433104700991147127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826783622069800660764751 11740175433104700991147127)
              ·
                refine ⟨17610263149657051486720691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740175433104700991147127 17610263149657051486720691)
                ·
                  refine ⟨26415394724485577230081037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17610263149657051486720691 26415394724485577230081037)
                  ·
                    refine ⟨9905773021682091461280389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26415394724485577230081037 9905773021682091461280389)
                    ·
                      refine ⟨1857332441565392148990073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9905773021682091461280389 1857332441565392148990073)
                      ·
                        rfl

theorem cell23_3617142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3617142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617142 prefixEnd_3617142 := by exact prefixLift 3617142
  have htrace : WordTrace (prefixWord ++ tailWord_3617142) baseStart_3617142 baseEnd_3617142 := by
    simpa [prefixWord, tailWord_3617142, baseEnd_3617142] using wordTrace_append hprefix tailTrace_3617142
  have hstable : (prefixWord ++ tailWord_3617142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617142).length < 2 ^ (prefixWord ++ tailWord_3617142).sum := by decide
  have hdescent : baseEnd_3617142 < baseStart_3617142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2]
def baseStart_3617168 : Nat := 118140960795 + 3617168 * 2 ^ 59
def prefixEnd_3617168 : Nat := 4983230072969 + 3 ^ 40 * 3617168 * 2
def baseEnd_3617168 : Nat := 1857345792062409047264953

theorem tailTrace_3617168 : CollatzResearch.WordTrace tailWord_3617168 prefixEnd_3617168 1857345792062409047264953 := by
  unfold tailWord_3617168
  simp only [CollatzResearch.WordTrace]
  refine ⟨65964477679812786978438079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87952636906417049304584105 65964477679812786978438079)
  ·
    refine ⟨98946716519719180467657119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65964477679812786978438079 98946716519719180467657119)
    ·
      refine ⟨148420074779578770701485679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98946716519719180467657119 148420074779578770701485679)
      ·
        refine ⟨222630112169368156052228519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148420074779578770701485679 222630112169368156052228519)
        ·
          refine ⟨333945168254052234078342779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222630112169368156052228519 333945168254052234078342779)
          ·
            refine ⟨500917752381078351117514169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333945168254052234078342779 500917752381078351117514169)
            ·
              refine ⟨375688314285808763338135627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500917752381078351117514169 375688314285808763338135627)
              ·
                refine ⟨563532471428713145007203441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375688314285808763338135627 563532471428713145007203441)
                ·
                  refine ⟨422649353571534858755402581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563532471428713145007203441 422649353571534858755402581)
                  ·
                    refine ⟨2476461056083212063019937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 422649353571534858755402581 2476461056083212063019937)
                    ·
                      refine ⟨1857345792062409047264953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476461056083212063019937 1857345792062409047264953)
                      ·
                        rfl

theorem cell23_3617168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2].length) (baseStart_3617168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617168 prefixEnd_3617168 := by exact prefixLift 3617168
  have htrace : WordTrace (prefixWord ++ tailWord_3617168) baseStart_3617168 baseEnd_3617168 := by
    simpa [prefixWord, tailWord_3617168, baseEnd_3617168] using wordTrace_append hprefix tailTrace_3617168
  have hstable : (prefixWord ++ tailWord_3617168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617168).length < 2 ^ (prefixWord ++ tailWord_3617168).sum := by decide
  have hdescent : baseEnd_3617168 < baseStart_3617168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617175 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3617175 : Nat := 118140960795 + 3617175 * 2 ^ 59
def prefixEnd_3617175 : Nat := 4983230072969 + 3 ^ 40 * 3617175 * 2
def baseEnd_3617175 : Nat := 1857349386426990519877421

theorem tailTrace_3617175 : CollatzResearch.WordTrace tailWord_3617175 prefixEnd_3617175 1857349386426990519877421 := by
  unfold tailWord_3617175
  simp only [CollatzResearch.WordTrace]
  refine ⟨131929210670600214152380979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87952807113733476101587319 131929210670600214152380979)
  ·
    refine ⟨197893816005900321228571469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131929210670600214152380979 197893816005900321228571469)
    ·
      refine ⟨74210181002212620460714301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197893816005900321228571469 74210181002212620460714301)
      ·
        refine ⟨27828817875829732672767863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74210181002212620460714301 27828817875829732672767863)
        ·
          refine ⟨41743226813744599009151795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27828817875829732672767863 41743226813744599009151795)
          ·
            refine ⟨62614840220616898513727693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41743226813744599009151795 62614840220616898513727693)
            ·
              refine ⟨23480565082731336942647885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62614840220616898513727693 23480565082731336942647885)
              ·
                refine ⟨8805211906024251353492957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23480565082731336942647885 8805211906024251353492957)
                ·
                  refine ⟨3301954464759094257559859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8805211906024251353492957 3301954464759094257559859)
                  ·
                    refine ⟨4952931697138641386339789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301954464759094257559859 4952931697138641386339789)
                    ·
                      refine ⟨1857349386426990519877421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952931697138641386339789 1857349386426990519877421)
                      ·
                        rfl

theorem cell23_3617175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3617175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617175 prefixEnd_3617175 := by exact prefixLift 3617175
  have htrace : WordTrace (prefixWord ++ tailWord_3617175) baseStart_3617175 baseEnd_3617175 := by
    simpa [prefixWord, tailWord_3617175, baseEnd_3617175] using wordTrace_append hprefix tailTrace_3617175
  have hstable : (prefixWord ++ tailWord_3617175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617175).length < 2 ^ (prefixWord ++ tailWord_3617175).sum := by decide
  have hdescent : baseEnd_3617175 < baseStart_3617175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617209 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3617209 : Nat := 118140960795 + 3617209 * 2 ^ 59
def prefixEnd_3617209 : Nat := 4983230072969 + 3 ^ 40 * 3617209 * 2
def baseEnd_3617209 : Nat := 1857366844769243386852265

theorem tailTrace_3617209 : CollatzResearch.WordTrace tailWord_3617209 prefixEnd_3617209 1857366844769243386852265 := by
  unfold tailWord_3617209
  simp only [CollatzResearch.WordTrace]
  refine ⟨131930450752477037959118681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87953633834984691972745787 131930450752477037959118681)
  ·
    refine ⟨98947838064357778469339011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131930450752477037959118681 98947838064357778469339011)
    ·
      refine ⟨148421757096536667704008517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98947838064357778469339011 148421757096536667704008517)
      ·
        refine ⟨27829079455600625194501597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148421757096536667704008517 27829079455600625194501597)
        ·
          refine ⟨10435904795850234447938099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27829079455600625194501597 10435904795850234447938099)
          ·
            refine ⟨15653857193775351671907149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435904795850234447938099 15653857193775351671907149)
            ·
              refine ⟨5870196447665756876965181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15653857193775351671907149 5870196447665756876965181)
              ·
                refine ⟨2201323667874658828861943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5870196447665756876965181 2201323667874658828861943)
                ·
                  refine ⟨3301985501811988243292915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201323667874658828861943 3301985501811988243292915)
                  ·
                    refine ⟨4952978252717982364939373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301985501811988243292915 4952978252717982364939373)
                    ·
                      refine ⟨1857366844769243386852265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4952978252717982364939373 1857366844769243386852265)
                      ·
                        rfl

theorem cell23_3617209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3617209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617209 prefixEnd_3617209 := by exact prefixLift 3617209
  have htrace : WordTrace (prefixWord ++ tailWord_3617209) baseStart_3617209 baseEnd_3617209 := by
    simpa [prefixWord, tailWord_3617209, baseEnd_3617209] using wordTrace_append hprefix tailTrace_3617209
  have hstable : (prefixWord ++ tailWord_3617209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617209).length < 2 ^ (prefixWord ++ tailWord_3617209).sum := by decide
  have hdescent : baseEnd_3617209 < baseStart_3617209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617211 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_3617211 : Nat := 118140960795 + 3617211 * 2 ^ 59
def prefixEnd_3617211 : Nat := 4983230072969 + 3 ^ 40 * 3617211 * 2
def baseEnd_3617211 : Nat := 1857367871730552379027255

theorem tailTrace_3617211 : CollatzResearch.WordTrace tailWord_3617211 prefixEnd_3617211 1857367871730552379027255 := by
  unfold tailWord_3617211
  simp only [CollatzResearch.WordTrace]
  refine ⟨131930523698469792300691487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87953682465646528200460991 131930523698469792300691487)
  ·
    refine ⟨197895785547704688451037231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131930523698469792300691487 197895785547704688451037231)
    ·
      refine ⟨296843678321557032676555847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197895785547704688451037231 296843678321557032676555847)
      ·
        refine ⟨445265517482335549014833771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296843678321557032676555847 445265517482335549014833771)
        ·
          refine ⟨667898276223503323522250657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445265517482335549014833771 667898276223503323522250657)
          ·
            refine ⟨500923707167627492641687993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667898276223503323522250657 500923707167627492641687993)
            ·
              refine ⟨375692780375720619481265995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500923707167627492641687993 375692780375720619481265995)
              ·
                refine ⟨563539170563580929221898993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375692780375720619481265995 563539170563580929221898993)
                ·
                  refine ⟨422654377922685696916424245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563539170563580929221898993 422654377922685696916424245)
                  ·
                    refine ⟨39623847930251784085914773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422654377922685696916424245 39623847930251784085914773)
                    ·
                      refine ⟨1857367871730552379027255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39623847930251784085914773 1857367871730552379027255)
                      ·
                        rfl

theorem cell23_3617211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_3617211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617211 prefixEnd_3617211 := by exact prefixLift 3617211
  have htrace : WordTrace (prefixWord ++ tailWord_3617211) baseStart_3617211 baseEnd_3617211 := by
    simpa [prefixWord, tailWord_3617211, baseEnd_3617211] using wordTrace_append hprefix tailTrace_3617211
  have hstable : (prefixWord ++ tailWord_3617211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617211).length < 2 ^ (prefixWord ++ tailWord_3617211).sum := by decide
  have hdescent : baseEnd_3617211 < baseStart_3617211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617245 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3617245 : Nat := 118140960795 + 3617245 * 2 ^ 59
def prefixEnd_3617245 : Nat := 4983230072969 + 3 ^ 40 * 3617245 * 2
def baseEnd_3617245 : Nat := 1857385330072805246002099

theorem tailTrace_3617245 : CollatzResearch.WordTrace tailWord_3617245 prefixEnd_3617245 1857385330072805246002099 := by
  unfold tailWord_3617245
  simp only [CollatzResearch.WordTrace]
  refine ⟨131931763780346616107429189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87954509186897744071619459 131931763780346616107429189)
  ·
    refine ⟨24737205708814990520142973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131931763780346616107429189 24737205708814990520142973)
    ·
      refine ⟨9276452140805621445053615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24737205708814990520142973 9276452140805621445053615)
      ·
        refine ⟨13914678211208432167580423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276452140805621445053615 13914678211208432167580423)
        ·
          refine ⟨20872017316812648251370635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914678211208432167580423 20872017316812648251370635)
          ·
            refine ⟨31308025975218972377055953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872017316812648251370635 31308025975218972377055953)
            ·
              refine ⟨23481019481414229282791965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31308025975218972377055953 23481019481414229282791965)
              ·
                refine ⟨8805382305530335981046987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23481019481414229282791965 8805382305530335981046987)
                ·
                  refine ⟨13208073458295503971570481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805382305530335981046987 13208073458295503971570481)
                  ·
                    refine ⟨9906055093721627978677861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13208073458295503971570481 9906055093721627978677861)
                    ·
                      refine ⟨1857385330072805246002099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9906055093721627978677861 1857385330072805246002099)
                      ·
                        rfl

theorem cell23_3617245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3617245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617245 prefixEnd_3617245 := by exact prefixLift 3617245
  have htrace : WordTrace (prefixWord ++ tailWord_3617245) baseStart_3617245 baseEnd_3617245 := by
    simpa [prefixWord, tailWord_3617245, baseEnd_3617245] using wordTrace_append hprefix tailTrace_3617245
  have hstable : (prefixWord ++ tailWord_3617245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617245).length < 2 ^ (prefixWord ++ tailWord_3617245).sum := by decide
  have hdescent : baseEnd_3617245 < baseStart_3617245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617265 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3617265 : Nat := 118140960795 + 3617265 * 2 ^ 59
def prefixEnd_3617265 : Nat := 4983230072969 + 3 ^ 40 * 3617265 * 2
def baseEnd_3617265 : Nat := 1857395599685895167752007

theorem tailTrace_3617265 : CollatzResearch.WordTrace tailWord_3617265 prefixEnd_3617265 1857395599685895167752007 := by
  unfold tailWord_3617265
  simp only [CollatzResearch.WordTrace]
  refine ⟨131932493240274159523157249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87954995493516106348771499 131932493240274159523157249)
  ·
    refine ⟨98949369930205619642367937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131932493240274159523157249 98949369930205619642367937)
    ·
      refine ⟨74212027447654214731775953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98949369930205619642367937 74212027447654214731775953)
      ·
        refine ⟨55659020585740661048831965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74212027447654214731775953 55659020585740661048831965)
        ·
          refine ⟨20872132719652747893311987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55659020585740661048831965 20872132719652747893311987)
          ·
            refine ⟨31308199079479121839967981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872132719652747893311987 31308199079479121839967981)
            ·
              refine ⟨11740574654804670689987993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31308199079479121839967981 11740574654804670689987993)
              ·
                refine ⟨8805430991103503017490995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11740574654804670689987993 8805430991103503017490995)
                ·
                  refine ⟨13208146486655254526236493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805430991103503017490995 13208146486655254526236493)
                  ·
                    refine ⟨4953054932495720447338685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13208146486655254526236493 4953054932495720447338685)
                    ·
                      refine ⟨1857395599685895167752007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953054932495720447338685 1857395599685895167752007)
                      ·
                        rfl

theorem cell23_3617265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3617265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617265 prefixEnd_3617265 := by exact prefixLift 3617265
  have htrace : WordTrace (prefixWord ++ tailWord_3617265) baseStart_3617265 baseEnd_3617265 := by
    simpa [prefixWord, tailWord_3617265, baseEnd_3617265] using wordTrace_append hprefix tailTrace_3617265
  have hstable : (prefixWord ++ tailWord_3617265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617265).length < 2 ^ (prefixWord ++ tailWord_3617265).sum := by decide
  have hdescent : baseEnd_3617265 < baseStart_3617265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617269 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3617269 : Nat := 118140960795 + 3617269 * 2 ^ 59
def prefixEnd_3617269 : Nat := 4983230072969 + 3 ^ 40 * 3617269 * 2
def baseEnd_3617269 : Nat := 1857397653608513152101989

theorem tailTrace_3617269 : CollatzResearch.WordTrace tailWord_3617269 prefixEnd_3617269 1857397653608513152101989 := by
  unfold tailWord_3617269
  simp only [CollatzResearch.WordTrace]
  refine ⟨131932639132259668206302861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87955092754839778804201907 131932639132259668206302861)
  ·
    refine ⟨49474739674597375577363573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131932639132259668206302861 49474739674597375577363573)
    ·
      refine ⟨4638256844493503960377835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49474739674597375577363573 4638256844493503960377835)
      ·
        refine ⟨6957385266740255940566753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638256844493503960377835 6957385266740255940566753)
        ·
          refine ⟨5218038950055191955425065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957385266740255940566753 5218038950055191955425065)
          ·
            refine ⟨3913529212541393966568799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218038950055191955425065 3913529212541393966568799)
            ·
              refine ⟨5870293818812090949853199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913529212541393966568799 5870293818812090949853199)
              ·
                refine ⟨8805440728218136424779799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5870293818812090949853199 8805440728218136424779799)
                ·
                  refine ⟨13208161092327204637169699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8805440728218136424779799 13208161092327204637169699)
                  ·
                    refine ⟨19812241638490806955754549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13208161092327204637169699 19812241638490806955754549)
                    ·
                      refine ⟨1857397653608513152101989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19812241638490806955754549 1857397653608513152101989)
                      ·
                        rfl

theorem cell23_3617269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3617269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617269 prefixEnd_3617269 := by exact prefixLift 3617269
  have htrace : WordTrace (prefixWord ++ tailWord_3617269) baseStart_3617269 baseEnd_3617269 := by
    simpa [prefixWord, tailWord_3617269, baseEnd_3617269] using wordTrace_append hprefix tailTrace_3617269
  have hstable : (prefixWord ++ tailWord_3617269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617269).length < 2 ^ (prefixWord ++ tailWord_3617269).sum := by decide
  have hdescent : baseEnd_3617269 < baseStart_3617269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617275 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 7, 3, 2]
def baseStart_3617275 : Nat := 118140960795 + 3617275 * 2 ^ 59
def prefixEnd_3617275 : Nat := 4983230072969 + 3 ^ 40 * 3617275 * 2
def baseEnd_3617275 : Nat := 1857400734492440128626961

theorem tailTrace_3617275 : CollatzResearch.WordTrace tailWord_3617275 prefixEnd_3617275 1857400734492440128626961 := by
  unfold tailWord_3617275
  simp only [CollatzResearch.WordTrace]
  refine ⟨131932857970237931231021279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87955238646825287487347519 131932857970237931231021279)
  ·
    refine ⟨197899286955356896846531919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131932857970237931231021279 197899286955356896846531919)
    ·
      refine ⟨296848930433035345269797879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197899286955356896846531919 296848930433035345269797879)
      ·
        refine ⟨445273395649553017904696819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296848930433035345269797879 445273395649553017904696819)
        ·
          refine ⟨667910093474329526857045229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445273395649553017904696819 667910093474329526857045229)
          ·
            refine ⟨250466285052873572571391961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667910093474329526857045229 250466285052873572571391961)
            ·
              refine ⟨187849713789655179428543971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250466285052873572571391961 187849713789655179428543971)
              ·
                refine ⟨281774570684482769142815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187849713789655179428543971 281774570684482769142815957)
                ·
                  refine ⟨6604091500417564901784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281774570684482769142815957 6604091500417564901784749)
                  ·
                    refine ⟨2476534312656586838169281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6604091500417564901784749 2476534312656586838169281)
                    ·
                      refine ⟨1857400734492440128626961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476534312656586838169281 1857400734492440128626961)
                      ·
                        rfl

theorem cell23_3617275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3, 2].length) (baseStart_3617275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617275 prefixEnd_3617275 := by exact prefixLift 3617275
  have htrace : WordTrace (prefixWord ++ tailWord_3617275) baseStart_3617275 baseEnd_3617275 := by
    simpa [prefixWord, tailWord_3617275, baseEnd_3617275] using wordTrace_append hprefix tailTrace_3617275
  have hstable : (prefixWord ++ tailWord_3617275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617275).length < 2 ^ (prefixWord ++ tailWord_3617275).sum := by decide
  have hdescent : baseEnd_3617275 < baseStart_3617275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617286 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3617286 : Nat := 118140960795 + 3617286 * 2 ^ 59
def prefixEnd_3617286 : Nat := 4983230072969 + 3 ^ 40 * 3617286 * 2
def baseEnd_3617286 : Nat := 1857406382779639585589411

theorem tailTrace_3617286 : CollatzResearch.WordTrace tailWord_3617286 prefixEnd_3617286 1857406382779639585589411 := by
  unfold tailWord_3617286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122914349162440003427241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87955506115465386739781141 4122914349162440003427241)
  ·
    refine ⟨3092185761871830002570431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4122914349162440003427241 3092185761871830002570431)
    ·
      refine ⟨4638278642807745003855647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092185761871830002570431 4638278642807745003855647)
      ·
        refine ⟨6957417964211617505783471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638278642807745003855647 6957417964211617505783471)
        ·
          refine ⟨10436126946317426258675207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957417964211617505783471 10436126946317426258675207)
          ·
            refine ⟨15654190419476139388012811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436126946317426258675207 15654190419476139388012811)
            ·
              refine ⟨23481285629214209082019217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654190419476139388012811 23481285629214209082019217)
              ·
                refine ⟨17610964221910656811514413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23481285629214209082019217 17610964221910656811514413)
                ·
                  refine ⟨6604111583216496304317905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17610964221910656811514413 6604111583216496304317905)
                  ·
                    refine ⟨4953083687412372228238429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6604111583216496304317905 4953083687412372228238429)
                    ·
                      refine ⟨1857406382779639585589411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953083687412372228238429 1857406382779639585589411)
                      ·
                        rfl

theorem cell23_3617286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3617286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617286 prefixEnd_3617286 := by exact prefixLift 3617286
  have htrace : WordTrace (prefixWord ++ tailWord_3617286) baseStart_3617286 baseEnd_3617286 := by
    simpa [prefixWord, tailWord_3617286, baseEnd_3617286] using wordTrace_append hprefix tailTrace_3617286
  have hstable : (prefixWord ++ tailWord_3617286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617286).length < 2 ^ (prefixWord ++ tailWord_3617286).sum := by decide
  have hdescent : baseEnd_3617286 < baseStart_3617286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617292 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_3617292 : Nat := 118140960795 + 3617292 * 2 ^ 59
def prefixEnd_3617292 : Nat := 4983230072969 + 3 ^ 40 * 3617292 * 2
def baseEnd_3617292 : Nat := 1857409463663566562114383

theorem tailTrace_3617292 : CollatzResearch.WordTrace tailWord_3617292 prefixEnd_3617292 1857409463663566562114383 := by
  unfold tailWord_3617292
  simp only [CollatzResearch.WordTrace]
  refine ⟨65966739005588171567195065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87955652007450895422926753 65966739005588171567195065)
  ·
    refine ⟨49475054254191128675396299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65966739005588171567195065 49475054254191128675396299)
    ·
      refine ⟨74212581381286693013094449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49475054254191128675396299 74212581381286693013094449)
      ·
        refine ⟨55659436035965019759820837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74212581381286693013094449 55659436035965019759820837)
        ·
          refine ⟨10436144256743441204966407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55659436035965019759820837 10436144256743441204966407)
          ·
            refine ⟨15654216385115161807449611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436144256743441204966407 15654216385115161807449611)
            ·
              refine ⟨23481324577672742711174417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654216385115161807449611 23481324577672742711174417)
              ·
                refine ⟨17610993433254557033380813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23481324577672742711174417 17610993433254557033380813)
                ·
                  refine ⟨6604122537470458887517805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17610993433254557033380813 6604122537470458887517805)
                  ·
                    refine ⟨2476545951551422082819177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6604122537470458887517805 2476545951551422082819177)
                    ·
                      refine ⟨1857409463663566562114383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476545951551422082819177 1857409463663566562114383)
                      ·
                        rfl

theorem cell23_3617292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_3617292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617292 prefixEnd_3617292 := by exact prefixLift 3617292
  have htrace : WordTrace (prefixWord ++ tailWord_3617292) baseStart_3617292 baseEnd_3617292 := by
    simpa [prefixWord, tailWord_3617292, baseEnd_3617292] using wordTrace_append hprefix tailTrace_3617292
  have hstable : (prefixWord ++ tailWord_3617292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617292).length < 2 ^ (prefixWord ++ tailWord_3617292).sum := by decide
  have hdescent : baseEnd_3617292 < baseStart_3617292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 4, 2]
def baseStart_3617305 : Nat := 118140960795 + 3617305 * 2 ^ 59
def prefixEnd_3617305 : Nat := 4983230072969 + 3 ^ 40 * 3617305 * 2
def baseEnd_3617305 : Nat := 1857416138912075011251823

theorem tailTrace_3617305 : CollatzResearch.WordTrace tailWord_3617305 prefixEnd_3617305 1857416138912075011251823 := by
  unfold tailWord_3617305
  simp only [CollatzResearch.WordTrace]
  refine ⟨131933952160129246354613369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87955968106752830903075579 131933952160129246354613369)
  ·
    refine ⟨98950464120096934765960027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131933952160129246354613369 98950464120096934765960027)
    ·
      refine ⟨148425696180145402148940041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98950464120096934765960027 148425696180145402148940041)
      ·
        refine ⟨111319272135109051611705031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148425696180145402148940041 111319272135109051611705031)
        ·
          refine ⟨166978908202663577417557547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111319272135109051611705031 166978908202663577417557547)
          ·
            refine ⟨250468362303995366126336321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166978908202663577417557547 250468362303995366126336321)
            ·
              refine ⟨187851271727996524594752241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250468362303995366126336321 187851271727996524594752241)
              ·
                refine ⟨140888453795997393446064181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187851271727996524594752241 140888453795997393446064181)
                ·
                  refine ⟨13208292543374755635568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140888453795997393446064181 13208292543374755635568517)
                  ·
                    refine ⟨2476554851882766681669097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13208292543374755635568517 2476554851882766681669097)
                    ·
                      refine ⟨1857416138912075011251823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476554851882766681669097 1857416138912075011251823)
                      ·
                        rfl

theorem cell23_3617305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_3617305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617305 prefixEnd_3617305 := by exact prefixLift 3617305
  have htrace : WordTrace (prefixWord ++ tailWord_3617305) baseStart_3617305 baseEnd_3617305 := by
    simpa [prefixWord, tailWord_3617305, baseEnd_3617305] using wordTrace_append hprefix tailTrace_3617305
  have hstable : (prefixWord ++ tailWord_3617305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617305).length < 2 ^ (prefixWord ++ tailWord_3617305).sum := by decide
  have hdescent : baseEnd_3617305 < baseStart_3617305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617326 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_3617326 : Nat := 118140960795 + 3617326 * 2 ^ 59
def prefixEnd_3617326 : Nat := 4983230072969 + 3 ^ 40 * 3617326 * 2
def baseEnd_3617326 : Nat := 1857426922005819429089227

theorem tailTrace_3617326 : CollatzResearch.WordTrace tailWord_3617326 prefixEnd_3617326 1857426922005819429089227 := by
  unfold tailWord_3617326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491839761631645867640979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87956478728702111294085221 16491839761631645867640979)
  ·
    refine ⟨24737759642447468801461469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16491839761631645867640979 24737759642447468801461469)
    ·
      refine ⟨9276659865917800800548051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24737759642447468801461469 9276659865917800800548051)
      ·
        refine ⟨13914989798876701200822077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276659865917800800548051 13914989798876701200822077)
        ·
          refine ⟨5218121174578762950308279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13914989798876701200822077 5218121174578762950308279)
          ·
            refine ⟨7827181761868144425462419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218121174578762950308279 7827181761868144425462419)
            ·
              refine ⟨11740772642802216638193629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827181761868144425462419 11740772642802216638193629)
              ·
                refine ⟨4402789741050831239322611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11740772642802216638193629 4402789741050831239322611)
                ·
                  refine ⟨6604184611576246858983917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402789741050831239322611 6604184611576246858983917)
                  ·
                    refine ⟨2476569229341092572118969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6604184611576246858983917 2476569229341092572118969)
                    ·
                      refine ⟨1857426922005819429089227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476569229341092572118969 1857426922005819429089227)
                      ·
                        rfl

theorem cell23_3617326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_3617326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617326 prefixEnd_3617326 := by exact prefixLift 3617326
  have htrace : WordTrace (prefixWord ++ tailWord_3617326) baseStart_3617326 baseEnd_3617326 := by
    simpa [prefixWord, tailWord_3617326, baseEnd_3617326] using wordTrace_append hprefix tailTrace_3617326
  have hstable : (prefixWord ++ tailWord_3617326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617326).length < 2 ^ (prefixWord ++ tailWord_3617326).sum := by decide
  have hdescent : baseEnd_3617326 < baseStart_3617326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617345 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 7]
def baseStart_3617345 : Nat := 118140960795 + 3617345 * 2 ^ 59
def prefixEnd_3617345 : Nat := 4983230072969 + 3 ^ 40 * 3617345 * 2
def baseEnd_3617345 : Nat := 206381853126472761639071

theorem tailTrace_3617345 : CollatzResearch.WordTrace tailWord_3617345 prefixEnd_3617345 206381853126472761639071 := by
  unfold tailWord_3617345
  simp only [CollatzResearch.WordTrace]
  refine ⟨131935411079984333186069489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87956940719989555457379659 131935411079984333186069489)
  ·
    refine ⟨98951558309988249889552117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131935411079984333186069489 98951558309988249889552117)
    ·
      refine ⟨9276708591561398427145511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98951558309988249889552117 9276708591561398427145511)
      ·
        refine ⟨13915062887342097640718267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276708591561398427145511 13915062887342097640718267)
        ·
          refine ⟨20872594331013146461077401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13915062887342097640718267 20872594331013146461077401)
          ·
            refine ⟨15654445748259859845808051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20872594331013146461077401 15654445748259859845808051)
            ·
              refine ⟨23481668622389789768712077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654445748259859845808051 23481668622389789768712077)
              ·
                refine ⟨8805625733396171163267029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23481668622389789768712077 8805625733396171163267029)
                ·
                  refine ⟨206381853126472761639071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8805625733396171163267029 206381853126472761639071)
                  ·
                    rfl

theorem cell23_3617345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_3617345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617345 prefixEnd_3617345 := by exact prefixLift 3617345
  have htrace : WordTrace (prefixWord ++ tailWord_3617345) baseStart_3617345 baseEnd_3617345 := by
    simpa [prefixWord, tailWord_3617345, baseEnd_3617345] using wordTrace_append hprefix tailTrace_3617345
  have hstable : (prefixWord ++ tailWord_3617345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617345).length < 2 ^ (prefixWord ++ tailWord_3617345).sum := by decide
  have hdescent : baseEnd_3617345 < baseStart_3617345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617355 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3]
def baseStart_3617355 : Nat := 118140960795 + 3617355 * 2 ^ 59
def prefixEnd_3617355 : Nat := 4983230072969 + 3 ^ 40 * 3617355 * 2
def baseEnd_3617355 : Nat := 1857441812944799815626593

theorem tailTrace_3617355 : CollatzResearch.WordTrace tailWord_3617355 prefixEnd_3617355 1857441812944799815626593 := by
  unfold tailWord_3617355
  simp only [CollatzResearch.WordTrace]
  refine ⟨131935775809948104893933519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87957183873298736595955679 131935775809948104893933519)
  ·
    refine ⟨197903663714922157340900279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131935775809948104893933519 197903663714922157340900279)
    ·
      refine ⟨296855495572383236011350419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197903663714922157340900279 296855495572383236011350419)
      ·
        refine ⟨445283243358574854017025629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296855495572383236011350419 445283243358574854017025629)
        ·
          refine ⟨166981216259465570256384611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445283243358574854017025629 166981216259465570256384611)
          ·
            refine ⟨250471824389198355384576917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166981216259465570256384611 250471824389198355384576917)
            ·
              refine ⟨11740866768243672908652043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250471824389198355384576917 11740866768243672908652043)
              ·
                refine ⟨17611300152365509362978065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11740866768243672908652043 17611300152365509362978065)
                ·
                  refine ⟨13208475114274132022233549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17611300152365509362978065 13208475114274132022233549)
                  ·
                    refine ⟨4953178167852799508337581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13208475114274132022233549 4953178167852799508337581)
                    ·
                      refine ⟨1857441812944799815626593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953178167852799508337581 1857441812944799815626593)
                      ·
                        rfl

theorem cell23_3617355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].length) (baseStart_3617355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617355 prefixEnd_3617355 := by exact prefixLift 3617355
  have htrace : WordTrace (prefixWord ++ tailWord_3617355) baseStart_3617355 baseEnd_3617355 := by
    simpa [prefixWord, tailWord_3617355, baseEnd_3617355] using wordTrace_append hprefix tailTrace_3617355
  have hstable : (prefixWord ++ tailWord_3617355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617355).length < 2 ^ (prefixWord ++ tailWord_3617355).sum := by decide
  have hdescent : baseEnd_3617355 < baseStart_3617355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617356 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3617356 : Nat := 118140960795 + 3617356 * 2 ^ 59
def prefixEnd_3617356 : Nat := 4983230072969 + 3 ^ 40 * 3617356 * 2
def baseEnd_3617356 : Nat := 1857442326425454311714089

theorem tailTrace_3617356 : CollatzResearch.WordTrace tailWord_3617356 prefixEnd_3617356 1857442326425454311714089 := by
  unfold tailWord_3617356
  simp only [CollatzResearch.WordTrace]
  refine ⟨65967906141472241032359961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87957208188629654709813281 65967906141472241032359961)
  ·
    refine ⟨49475929606104180774269971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65967906141472241032359961 49475929606104180774269971)
    ·
      refine ⟨74213894409156271161404957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49475929606104180774269971 74213894409156271161404957)
      ·
        refine ⟨27830210403433601685526859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74213894409156271161404957 27830210403433601685526859)
        ·
          refine ⟨41745315605150402528290289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27830210403433601685526859 41745315605150402528290289)
          ·
            refine ⟨31308986703862801896217717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41745315605150402528290289 31308986703862801896217717)
            ·
              refine ⟨2935217503487137677770411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31308986703862801896217717 2935217503487137677770411)
              ·
                refine ⟨4402826255230706516655617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935217503487137677770411 4402826255230706516655617)
                ·
                  refine ⟨3302119691423029887491713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402826255230706516655617 3302119691423029887491713)
                  ·
                    refine ⟨2476589768567272415618785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302119691423029887491713 2476589768567272415618785)
                    ·
                      refine ⟨1857442326425454311714089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476589768567272415618785 1857442326425454311714089)
                      ·
                        rfl

theorem cell23_3617356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3617356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617356 prefixEnd_3617356 := by exact prefixLift 3617356
  have htrace : WordTrace (prefixWord ++ tailWord_3617356) baseStart_3617356 baseEnd_3617356 := by
    simpa [prefixWord, tailWord_3617356, baseEnd_3617356] using wordTrace_append hprefix tailTrace_3617356
  have hstable : (prefixWord ++ tailWord_3617356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617356).length < 2 ^ (prefixWord ++ tailWord_3617356).sum := by decide
  have hdescent : baseEnd_3617356 < baseStart_3617356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617392 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_3617392 : Nat := 118140960795 + 3617392 * 2 ^ 59
def prefixEnd_3617392 : Nat := 4983230072969 + 3 ^ 40 * 3617392 * 2
def baseEnd_3617392 : Nat := 619153603909672056954641

theorem tailTrace_3617392 : CollatzResearch.WordTrace tailWord_3617392 prefixEnd_3617392 619153603909672056954641 := by
  unfold tailWord_3617392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65968562655407030106515215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87958083540542706808686953 65968562655407030106515215)
  ·
    refine ⟨98952843983110545159772823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65968562655407030106515215 98952843983110545159772823)
    ·
      refine ⟨148429265974665817739659235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98952843983110545159772823 148429265974665817739659235)
      ·
        refine ⟨222643898961998726609488853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148429265974665817739659235 222643898961998726609488853)
        ·
          refine ⟨5218216381921845154909895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 222643898961998726609488853 5218216381921845154909895)
          ·
            refine ⟨7827324572882767732364843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218216381921845154909895 7827324572882767732364843)
            ·
              refine ⟨11740986859324151598547265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827324572882767732364843 11740986859324151598547265)
              ·
                refine ⟨8805740144493113698910449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11740986859324151598547265 8805740144493113698910449)
                ·
                  refine ⟨6604305108369835274182837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8805740144493113698910449 6604305108369835274182837)
                  ·
                    refine ⟨619153603909672056954641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6604305108369835274182837 619153603909672056954641)
                    ·
                      rfl

theorem cell23_3617392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_3617392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617392 prefixEnd_3617392 := by exact prefixLift 3617392
  have htrace : WordTrace (prefixWord ++ tailWord_3617392) baseStart_3617392 baseEnd_3617392 := by
    simpa [prefixWord, tailWord_3617392, baseEnd_3617392] using wordTrace_append hprefix tailTrace_3617392
  have hstable : (prefixWord ++ tailWord_3617392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617392).length < 2 ^ (prefixWord ++ tailWord_3617392).sum := by decide
  have hdescent : baseEnd_3617392 < baseStart_3617392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617422 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3617422 : Nat := 118140960795 + 3617422 * 2 ^ 59
def prefixEnd_3617422 : Nat := 4983230072969 + 3 ^ 40 * 3617422 * 2
def baseEnd_3617422 : Nat := 619158738716217017829595

theorem tailTrace_3617422 : CollatzResearch.WordTrace tailWord_3617422 prefixEnd_3617422 619158738716217017829595 := by
  unfold tailWord_3617422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492277437588171917077815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87958813000470250224415013 16492277437588171917077815)
  ·
    refine ⟨24738416156382257875616723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492277437588171917077815 24738416156382257875616723)
    ·
      refine ⟨37107624234573386813425085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24738416156382257875616723 37107624234573386813425085)
      ·
        refine ⟨13915359087965020055034407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37107624234573386813425085 13915359087965020055034407)
        ·
          refine ⟨20873038631947530082551611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13915359087965020055034407 20873038631947530082551611)
          ·
            refine ⟨31309557947921295123827417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20873038631947530082551611 31309557947921295123827417)
            ·
              refine ⟨23482168460940971342870563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31309557947921295123827417 23482168460940971342870563)
              ·
                refine ⟨35223252691411457014305845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482168460940971342870563 35223252691411457014305845)
                ·
                  refine ⟨3302179939819824095091173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35223252691411457014305845 3302179939819824095091173)
                  ·
                    refine ⟨619158738716217017829595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3302179939819824095091173 619158738716217017829595)
                    ·
                      rfl

theorem cell23_3617422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3617422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617422 prefixEnd_3617422 := by exact prefixLift 3617422
  have htrace : WordTrace (prefixWord ++ tailWord_3617422) baseStart_3617422 baseEnd_3617422 := by
    simpa [prefixWord, tailWord_3617422, baseEnd_3617422] using wordTrace_append hprefix tailTrace_3617422
  have hstable : (prefixWord ++ tailWord_3617422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617422).length < 2 ^ (prefixWord ++ tailWord_3617422).sum := by decide
  have hdescent : baseEnd_3617422 < baseStart_3617422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617482 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3617482 : Nat := 118140960795 + 3617482 * 2 ^ 59
def prefixEnd_3617482 : Nat := 4983230072969 + 3 ^ 40 * 3617482 * 2
def baseEnd_3617482 : Nat := 619169008329306939579503

theorem tailTrace_3617482 : CollatzResearch.WordTrace tailWord_3617482 prefixEnd_3617482 619169008329306939579503 := by
  unfold tailWord_3617482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985101970122001395951675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87960271920325337055871133 32985101970122001395951675)
  ·
    refine ⟨49477652955183002093927513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32985101970122001395951675 49477652955183002093927513)
    ·
      refine ⟨37108239716387251570445635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49477652955183002093927513 37108239716387251570445635)
      ·
        refine ⟨55662359574580877355668453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37108239716387251570445635 55662359574580877355668453)
        ·
          refine ⟨10436692420233914504187835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55662359574580877355668453 10436692420233914504187835)
          ·
            refine ⟨15655038630350871756281753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436692420233914504187835 15655038630350871756281753)
            ·
              refine ⟨11741278972763153817211315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15655038630350871756281753 11741278972763153817211315)
              ·
                refine ⟨17611918459144730725816973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741278972763153817211315 17611918459144730725816973)
                ·
                  refine ⟨6604469422179274022181365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17611918459144730725816973 6604469422179274022181365)
                  ·
                    refine ⟨619169008329306939579503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6604469422179274022181365 619169008329306939579503)
                    ·
                      rfl

theorem cell23_3617482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3617482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617482 prefixEnd_3617482 := by exact prefixLift 3617482
  have htrace : WordTrace (prefixWord ++ tailWord_3617482) baseStart_3617482 baseEnd_3617482 := by
    simpa [prefixWord, tailWord_3617482, baseEnd_3617482] using wordTrace_append hprefix tailTrace_3617482
  have hstable : (prefixWord ++ tailWord_3617482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617482).length < 2 ^ (prefixWord ++ tailWord_3617482).sum := by decide
  have hdescent : baseEnd_3617482 < baseStart_3617482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617496 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_3617496 : Nat := 118140960795 + 3617496 * 2 ^ 59
def prefixEnd_3617496 : Nat := 4983230072969 + 3 ^ 40 * 3617496 * 2
def baseEnd_3617496 : Nat := 1857514213717083763963445

theorem tailTrace_3617496 : CollatzResearch.WordTrace tailWord_3617496 prefixEnd_3617496 1857514213717083763963445 := by
  unfold tailWord_3617496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65970459251218642987408171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87960612334958190649877561 65970459251218642987408171)
  ·
    refine ⟨98955688876827964481112257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65970459251218642987408171 98955688876827964481112257)
    ·
      refine ⟨74216766657620973360834193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98955688876827964481112257 74216766657620973360834193)
      ·
        refine ⟨55662574993215730020625645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74216766657620973360834193 55662574993215730020625645)
        ·
          refine ⟨20873465622455898757734617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55662574993215730020625645 20873465622455898757734617)
          ·
            refine ⟨15655099216841924068300963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20873465622455898757734617 15655099216841924068300963)
            ·
              refine ⟨23482648825262886102451445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655099216841924068300963 23482648825262886102451445)
              ·
                refine ⟨2201498327368395572104823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23482648825262886102451445 2201498327368395572104823)
                ·
                  refine ⟨3302247491052593358157235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201498327368395572104823 3302247491052593358157235)
                  ·
                    refine ⟨4953371236578890037235853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302247491052593358157235 4953371236578890037235853)
                    ·
                      refine ⟨1857514213717083763963445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953371236578890037235853 1857514213717083763963445)
                      ·
                        rfl

theorem cell23_3617496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_3617496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617496 prefixEnd_3617496 := by exact prefixLift 3617496
  have htrace : WordTrace (prefixWord ++ tailWord_3617496) baseStart_3617496 baseEnd_3617496 := by
    simpa [prefixWord, tailWord_3617496, baseEnd_3617496] using wordTrace_append hprefix tailTrace_3617496
  have hstable : (prefixWord ++ tailWord_3617496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617496).length < 2 ^ (prefixWord ++ tailWord_3617496).sum := by decide
  have hdescent : baseEnd_3617496 < baseStart_3617496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617515 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_3617515 : Nat := 118140960795 + 3617515 * 2 ^ 59
def prefixEnd_3617515 : Nat := 4983230072969 + 3 ^ 40 * 3617515 * 2
def baseEnd_3617515 : Nat := 1857523969849519189625857

theorem tailTrace_3617515 : CollatzResearch.WordTrace tailWord_3617515 prefixEnd_3617515 1857523969849519189625857 := by
  unfold tailWord_3617515
  simp only [CollatzResearch.WordTrace]
  refine ⟨131941611489368452219757999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87961074326245634813171999 131941611489368452219757999)
  ·
    refine ⟨197912417234052678329636999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131941611489368452219757999 197912417234052678329636999)
    ·
      refine ⟨296868625851079017494455499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197912417234052678329636999 296868625851079017494455499)
      ·
        refine ⟨445302938776618526241683249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296868625851079017494455499 445302938776618526241683249)
        ·
          refine ⟨333977204082463894681262437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445302938776618526241683249 333977204082463894681262437)
          ·
            refine ⟨62620725765461980252736707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333977204082463894681262437 62620725765461980252736707)
            ·
              refine ⟨93931088648192970379105061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62620725765461980252736707 93931088648192970379105061)
              ·
                refine ⟨17612079121536181946082199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93931088648192970379105061 17612079121536181946082199)
                ·
                  refine ⟨26418118682304272919123299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17612079121536181946082199 26418118682304272919123299)
                  ·
                    refine ⟨39627178023456409378684949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26418118682304272919123299 39627178023456409378684949)
                    ·
                      refine ⟨1857523969849519189625857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39627178023456409378684949 1857523969849519189625857)
                      ·
                        rfl

theorem cell23_3617515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_3617515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617515 prefixEnd_3617515 := by exact prefixLift 3617515
  have htrace : WordTrace (prefixWord ++ tailWord_3617515) baseStart_3617515 baseEnd_3617515 := by
    simpa [prefixWord, tailWord_3617515, baseEnd_3617515] using wordTrace_append hprefix tailTrace_3617515
  have hstable : (prefixWord ++ tailWord_3617515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617515).length < 2 ^ (prefixWord ++ tailWord_3617515).sum := by decide
  have hdescent : baseEnd_3617515 < baseStart_3617515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617522 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3617522 : Nat := 118140960795 + 3617522 * 2 ^ 59
def prefixEnd_3617522 : Nat := 4983230072969 + 3 ^ 40 * 3617522 * 2
def baseEnd_3617522 : Nat := 1857527564214100662238325

theorem tailTrace_3617522 : CollatzResearch.WordTrace tailWord_3617522 prefixEnd_3617522 1857527564214100662238325 := by
  unfold tailWord_3617522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985466700085773103815705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87961244533562061610175213 32985466700085773103815705)
  ·
    refine ⟨24739100025064329827861779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32985466700085773103815705 24739100025064329827861779)
    ·
      refine ⟨37108650037596494741792669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24739100025064329827861779 37108650037596494741792669)
      ·
        refine ⟨13915743764098685528172251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37108650037596494741792669 13915743764098685528172251)
        ·
          refine ⟨20873615646148028292258377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13915743764098685528172251 20873615646148028292258377)
          ·
            refine ⟨15655211734611021219193783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20873615646148028292258377 15655211734611021219193783)
            ·
              refine ⟨23482817601916531828790675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655211734611021219193783 23482817601916531828790675)
              ·
                refine ⟨35224226402874797743186013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482817601916531828790675 35224226402874797743186013)
                ·
                  refine ⟨13209084901078049153694755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35224226402874797743186013 13209084901078049153694755)
                  ·
                    refine ⟨19813627351617073730542133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13209084901078049153694755 19813627351617073730542133)
                    ·
                      refine ⟨1857527564214100662238325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19813627351617073730542133 1857527564214100662238325)
                      ·
                        rfl

theorem cell23_3617522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3617522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617522 prefixEnd_3617522 := by exact prefixLift 3617522
  have htrace : WordTrace (prefixWord ++ tailWord_3617522) baseStart_3617522 baseEnd_3617522 := by
    simpa [prefixWord, tailWord_3617522, baseEnd_3617522] using wordTrace_append hprefix tailTrace_3617522
  have hstable : (prefixWord ++ tailWord_3617522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617522).length < 2 ^ (prefixWord ++ tailWord_3617522).sum := by decide
  have hdescent : baseEnd_3617522 < baseStart_3617522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617532 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3617532 : Nat := 118140960795 + 3617532 * 2 ^ 59
def prefixEnd_3617532 : Nat := 4983230072969 + 3 ^ 40 * 3617532 * 2
def baseEnd_3617532 : Nat := 1857532699020645623113279

theorem tailTrace_3617532 : CollatzResearch.WordTrace tailWord_3617532 prefixEnd_3617532 1857532699020645623113279 := by
  unfold tailWord_3617532
  simp only [CollatzResearch.WordTrace]
  refine ⟨65971115765153432061563425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87961487686871242748751233 65971115765153432061563425)
  ·
    refine ⟨49478336823865074046172569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65971115765153432061563425 49478336823865074046172569)
    ·
      refine ⟨37108752617898805534629427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49478336823865074046172569 37108752617898805534629427)
      ·
        refine ⟨55663128926848208301944141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37108752617898805534629427 55663128926848208301944141)
        ·
          refine ⟨20873673347568078113229053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55663128926848208301944141 20873673347568078113229053)
          ·
            refine ⟨7827627505338029292460895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20873673347568078113229053 7827627505338029292460895)
            ·
              refine ⟨11741441258007043938691343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827627505338029292460895 11741441258007043938691343)
              ·
                refine ⟨17612161887010565908037015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741441258007043938691343 17612161887010565908037015)
                ·
                  refine ⟨26418242830515848862055523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17612161887010565908037015 26418242830515848862055523)
                  ·
                    refine ⟨39627364245773773293083285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26418242830515848862055523 39627364245773773293083285)
                    ·
                      refine ⟨1857532699020645623113279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39627364245773773293083285 1857532699020645623113279)
                      ·
                        rfl

theorem cell23_3617532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3617532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617532 prefixEnd_3617532 := by exact prefixLift 3617532
  have htrace : WordTrace (prefixWord ++ tailWord_3617532) baseStart_3617532 baseEnd_3617532 := by
    simpa [prefixWord, tailWord_3617532, baseEnd_3617532] using wordTrace_append hprefix tailTrace_3617532
  have hstable : (prefixWord ++ tailWord_3617532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617532).length < 2 ^ (prefixWord ++ tailWord_3617532).sum := by decide
  have hdescent : baseEnd_3617532 < baseStart_3617532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617553 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_3617553 : Nat := 118140960795 + 3617553 * 2 ^ 59
def prefixEnd_3617553 : Nat := 4983230072969 + 3 ^ 40 * 3617553 * 2
def baseEnd_3617553 : Nat := 1857543482114390040950683

theorem tailTrace_3617553 : CollatzResearch.WordTrace tailWord_3617553 prefixEnd_3617553 1857543482114390040950683 := by
  unfold tailWord_3617553
  simp only [CollatzResearch.WordTrace]
  refine ⟨131942997463230784709641313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87961998308820523139760875 131942997463230784709641313)
  ·
    refine ⟨98957248097423088532230985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131942997463230784709641313 98957248097423088532230985)
    ·
      refine ⟨74217936073067316399173239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98957248097423088532230985 74217936073067316399173239)
      ·
        refine ⟨111326904109600974598759859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74217936073067316399173239 111326904109600974598759859)
        ·
          refine ⟨166990356164401461898139789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111326904109600974598759859 166990356164401461898139789)
          ·
            refine ⟨62621383561650548211802421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166990356164401461898139789 62621383561650548211802421)
            ·
              refine ⟨5870754708904738894856477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62621383561650548211802421 5870754708904738894856477)
              ·
                refine ⟨2201533015839277085571179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5870754708904738894856477 2201533015839277085571179)
                ·
                  refine ⟨3302299523758915628356769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201533015839277085571179 3302299523758915628356769)
                  ·
                    refine ⟨2476724642819186721267577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302299523758915628356769 2476724642819186721267577)
                    ·
                      refine ⟨1857543482114390040950683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476724642819186721267577 1857543482114390040950683)
                      ·
                        rfl

theorem cell23_3617553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_3617553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617553 prefixEnd_3617553 := by exact prefixLift 3617553
  have htrace : WordTrace (prefixWord ++ tailWord_3617553) baseStart_3617553 baseEnd_3617553 := by
    simpa [prefixWord, tailWord_3617553, baseEnd_3617553] using wordTrace_append hprefix tailTrace_3617553
  have hstable : (prefixWord ++ tailWord_3617553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617553).length < 2 ^ (prefixWord ++ tailWord_3617553).sum := by decide
  have hdescent : baseEnd_3617553 < baseStart_3617553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617559 : List Nat := [1, 1, 3, 4, 4, 1, 9]
def baseStart_3617559 : Nat := 118140960795 + 3617559 * 2 ^ 59
def prefixEnd_3617559 : Nat := 4983230072969 + 3 ^ 40 * 3617559 * 2
def baseEnd_3617559 : Nat := 22932673617263173055255

theorem tailTrace_3617559 : CollatzResearch.WordTrace tailWord_3617559 prefixEnd_3617559 22932673617263173055255 := by
  unfold tailWord_3617559
  simp only [CollatzResearch.WordTrace]
  refine ⟨131943216301209047734359731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87962144200806031822906487 131943216301209047734359731)
  ·
    refine ⟨197914824451813571601539597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131943216301209047734359731 197914824451813571601539597)
    ·
      refine ⟨74218059169430089350577349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197914824451813571601539597 74218059169430089350577349)
      ·
        refine ⟨13915886094268141753233253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74218059169430089350577349 13915886094268141753233253)
        ·
          refine ⟨2609228642675276578731235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13915886094268141753233253 2609228642675276578731235)
          ·
            refine ⟨3913842964012914868096853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609228642675276578731235 3913842964012914868096853)
            ·
              refine ⟨22932673617263173055255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3913842964012914868096853 22932673617263173055255)
              ·
                rfl

theorem cell23_3617559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 9].length) (baseStart_3617559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617559 prefixEnd_3617559 := by exact prefixLift 3617559
  have htrace : WordTrace (prefixWord ++ tailWord_3617559) baseStart_3617559 baseEnd_3617559 := by
    simpa [prefixWord, tailWord_3617559, baseEnd_3617559] using wordTrace_append hprefix tailTrace_3617559
  have hstable : (prefixWord ++ tailWord_3617559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617559).length < 2 ^ (prefixWord ++ tailWord_3617559).sum := by decide
  have hdescent : baseEnd_3617559 < baseStart_3617559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617569 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3617569 : Nat := 118140960795 + 3617569 * 2 ^ 59
def prefixEnd_3617569 : Nat := 4983230072969 + 3 ^ 40 * 3617569 * 2
def baseEnd_3617569 : Nat := 1857551697804861978350609

theorem tailTrace_3617569 : CollatzResearch.WordTrace tailWord_3617569 prefixEnd_3617569 1857551697804861978350609 := by
  unfold tailWord_3617569
  simp only [CollatzResearch.WordTrace]
  refine ⟨131943581031172819442223761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87962387354115212961482507 131943581031172819442223761)
  ·
    refine ⟨98957685773379614581667821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131943581031172819442223761 98957685773379614581667821)
    ·
      refine ⟨37109132165017355468125433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98957685773379614581667821 37109132165017355468125433)
      ·
        refine ⟨27831849123763016601094075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37109132165017355468125433 27831849123763016601094075)
        ·
          refine ⟨41747773685644524901641113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27831849123763016601094075 41747773685644524901641113)
          ·
            refine ⟨31310830264233393676230835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41747773685644524901641113 31310830264233393676230835)
            ·
              refine ⟨46966245396350090514346253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31310830264233393676230835 46966245396350090514346253)
              ·
                refine ⟨17612342023631283942879845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46966245396350090514346253 17612342023631283942879845)
                ·
                  refine ⟨3302314129430865739289971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17612342023631283942879845 3302314129430865739289971)
                  ·
                    refine ⟨4953471194146298608934957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302314129430865739289971 4953471194146298608934957)
                    ·
                      refine ⟨1857551697804861978350609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953471194146298608934957 1857551697804861978350609)
                      ·
                        rfl

theorem cell23_3617569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3617569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617569 prefixEnd_3617569 := by exact prefixLift 3617569
  have htrace : WordTrace (prefixWord ++ tailWord_3617569) baseStart_3617569 baseEnd_3617569 := by
    simpa [prefixWord, tailWord_3617569, baseEnd_3617569] using wordTrace_append hprefix tailTrace_3617569
  have hstable : (prefixWord ++ tailWord_3617569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617569).length < 2 ^ (prefixWord ++ tailWord_3617569).sum := by decide
  have hdescent : baseEnd_3617569 < baseStart_3617569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617586 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3617586 : Nat := 118140960795 + 3617586 * 2 ^ 59
def prefixEnd_3617586 : Nat := 4983230072969 + 3 ^ 40 * 3617586 * 2
def baseEnd_3617586 : Nat := 1857560426975988411838031

theorem tailTrace_3617586 : CollatzResearch.WordTrace tailWord_3617586 prefixEnd_3617586 1857560426975988411838031 := by
  unfold tailWord_3617586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986050268027807836398153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87962800714740820897061741 32986050268027807836398153)
  ·
    refine ⟨24739537701020855877298615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32986050268027807836398153 24739537701020855877298615)
    ·
      refine ⟨37109306551531283815947923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24739537701020855877298615 37109306551531283815947923)
      ·
        refine ⟨55663959827296925723921885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37109306551531283815947923 55663959827296925723921885)
        ·
          refine ⟨20873984935236347146470707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55663959827296925723921885 20873984935236347146470707)
          ·
            refine ⟨31310977402854520719706061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20873984935236347146470707 31310977402854520719706061)
            ·
              refine ⟨11741616526070445269889773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31310977402854520719706061 11741616526070445269889773)
              ·
                refine ⟨4403106197276416976208665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11741616526070445269889773 4403106197276416976208665)
                ·
                  refine ⟨3302329647957312732156499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4403106197276416976208665 3302329647957312732156499)
                  ·
                    refine ⟨4953494471935969098234749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302329647957312732156499 4953494471935969098234749)
                    ·
                      refine ⟨1857560426975988411838031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953494471935969098234749 1857560426975988411838031)
                      ·
                        rfl

theorem cell23_3617586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3617586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617586 prefixEnd_3617586 := by exact prefixLift 3617586
  have htrace : WordTrace (prefixWord ++ tailWord_3617586) baseStart_3617586 baseEnd_3617586 := by
    simpa [prefixWord, tailWord_3617586, baseEnd_3617586] using wordTrace_append hprefix tailTrace_3617586
  have hstable : (prefixWord ++ tailWord_3617586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617586).length < 2 ^ (prefixWord ++ tailWord_3617586).sum := by decide
  have hdescent : baseEnd_3617586 < baseStart_3617586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617590 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3617590 : Nat := 118140960795 + 3617590 * 2 ^ 59
def prefixEnd_3617590 : Nat := 4983230072969 + 3 ^ 40 * 3617590 * 2
def baseEnd_3617590 : Nat := 1857562480898606396188013

theorem tailTrace_3617590 : CollatzResearch.WordTrace tailWord_3617590 prefixEnd_3617590 1857562480898606396188013 := by
  unfold tailWord_3617590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246521685256046251796139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87962897976064493352492149 8246521685256046251796139)
  ·
    refine ⟨12369782527884069377694209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8246521685256046251796139 12369782527884069377694209)
    ·
      refine ⟨9277336895913052033270657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12369782527884069377694209 9277336895913052033270657)
      ·
        refine ⟨6958002671934789024952993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9277336895913052033270657 6958002671934789024952993)
        ·
          refine ⟨5218502003951091768714745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958002671934789024952993 5218502003951091768714745)
          ·
            refine ⟨3913876502963318826536059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218502003951091768714745 3913876502963318826536059)
            ·
              refine ⟨5870814754444978239804089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913876502963318826536059 5870814754444978239804089)
              ·
                refine ⟨4403111065833733679853067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5870814754444978239804089 4403111065833733679853067)
                ·
                  refine ⟨6604666598750600519779601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403111065833733679853067 6604666598750600519779601)
                  ·
                    refine ⟨4953499949062950389834701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6604666598750600519779601 4953499949062950389834701)
                    ·
                      refine ⟨1857562480898606396188013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953499949062950389834701 1857562480898606396188013)
                      ·
                        rfl

theorem cell23_3617590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3617590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617590 prefixEnd_3617590 := by exact prefixLift 3617590
  have htrace : WordTrace (prefixWord ++ tailWord_3617590) baseStart_3617590 baseEnd_3617590 := by
    simpa [prefixWord, tailWord_3617590, baseEnd_3617590] using wordTrace_append hprefix tailTrace_3617590
  have hstable : (prefixWord ++ tailWord_3617590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617590).length < 2 ^ (prefixWord ++ tailWord_3617590).sum := by decide
  have hdescent : baseEnd_3617590 < baseStart_3617590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617595 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_3617595 : Nat := 118140960795 + 3617595 * 2 ^ 59
def prefixEnd_3617595 : Nat := 4983230072969 + 3 ^ 40 * 3617595 * 2
def baseEnd_3617595 : Nat := 1857565048301878876625489

theorem tailTrace_3617595 : CollatzResearch.WordTrace tailWord_3617595 prefixEnd_3617595 1857565048301878876625489 := by
  unfold tailWord_3617595
  simp only [CollatzResearch.WordTrace]
  refine ⟨131944529329078625882670239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87963019552719083921780159 131944529329078625882670239)
  ·
    refine ⟨197916793993617938824005359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131944529329078625882670239 197916793993617938824005359)
    ·
      refine ⟨296875190990426908236008039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197916793993617938824005359 296875190990426908236008039)
      ·
        refine ⟨445312786485640362354012059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296875190990426908236008039 445312786485640362354012059)
        ·
          refine ⟨667969179728460543531018089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445312786485640362354012059 667969179728460543531018089)
          ·
            refine ⟨500976884796345407648263567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667969179728460543531018089 500976884796345407648263567)
            ·
              refine ⟨751465327194518111472395351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500976884796345407648263567 751465327194518111472395351)
              ·
                refine ⟨1127197990791777167208593027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751465327194518111472395351 1127197990791777167208593027)
                ·
                  refine ⟨1690796986187665750812889541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127197990791777167208593027 1690796986187665750812889541)
                  ·
                    refine ⟨317024434910187328277416789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690796986187665750812889541 317024434910187328277416789)
                    ·
                      refine ⟨1857565048301878876625489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 317024434910187328277416789 1857565048301878876625489)
                      ·
                        rfl

theorem cell23_3617595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_3617595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617595 prefixEnd_3617595 := by exact prefixLift 3617595
  have htrace : WordTrace (prefixWord ++ tailWord_3617595) baseStart_3617595 baseEnd_3617595 := by
    simpa [prefixWord, tailWord_3617595, baseEnd_3617595] using wordTrace_append hprefix tailTrace_3617595
  have hstable : (prefixWord ++ tailWord_3617595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617595).length < 2 ^ (prefixWord ++ tailWord_3617595).sum := by decide
  have hdescent : baseEnd_3617595 < baseStart_3617595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617609 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 4, 2]
def baseStart_3617609 : Nat := 118140960795 + 3617609 * 2 ^ 59
def prefixEnd_3617609 : Nat := 4983230072969 + 3 ^ 40 * 3617609 * 2
def baseEnd_3617609 : Nat := 1857572237031041821850425

theorem tailTrace_3617609 : CollatzResearch.WordTrace tailWord_3617609 prefixEnd_3617609 1857572237031041821850425 := by
  unfold tailWord_3617609
  simp only [CollatzResearch.WordTrace]
  refine ⟨131945039951027906273679881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87963359967351937515786587 131945039951027906273679881)
  ·
    refine ⟨98958779963270929705259911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131945039951027906273679881 98958779963270929705259911)
    ·
      refine ⟨148438169944906394557889867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98958779963270929705259911 148438169944906394557889867)
      ·
        refine ⟨222657254917359591836834801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148438169944906394557889867 222657254917359591836834801)
        ·
          refine ⟨166992941188019693877626101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222657254917359591836834801 166992941188019693877626101)
          ·
            refine ⟨15655588236376846301027447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166992941188019693877626101 15655588236376846301027447)
            ·
              refine ⟨23483382354565269451541171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655588236376846301027447 23483382354565269451541171)
              ·
                refine ⟨35225073531847904177311757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23483382354565269451541171 35225073531847904177311757)
                ·
                  refine ⟨13209402574442964066491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35225073531847904177311757 13209402574442964066491909)
                  ·
                    refine ⟨2476762982708055762467233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13209402574442964066491909 2476762982708055762467233)
                    ·
                      refine ⟨1857572237031041821850425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476762982708055762467233 1857572237031041821850425)
                      ·
                        rfl

theorem cell23_3617609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4, 2].length) (baseStart_3617609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617609 prefixEnd_3617609 := by exact prefixLift 3617609
  have htrace : WordTrace (prefixWord ++ tailWord_3617609) baseStart_3617609 baseEnd_3617609 := by
    simpa [prefixWord, tailWord_3617609, baseEnd_3617609] using wordTrace_append hprefix tailTrace_3617609
  have hstable : (prefixWord ++ tailWord_3617609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617609).length < 2 ^ (prefixWord ++ tailWord_3617609).sum := by decide
  have hdescent : baseEnd_3617609 < baseStart_3617609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617632 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 7]
def baseStart_3617632 : Nat := 118140960795 + 3617632 * 2 ^ 59
def prefixEnd_3617632 : Nat := 4983230072969 + 3 ^ 40 * 3617632 * 2
def baseEnd_3617632 : Nat := 206398227454010581318091

theorem tailTrace_3617632 : CollatzResearch.WordTrace tailWord_3617632 prefixEnd_3617632 206398227454010581318091 := by
  unfold tailWord_3617632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65972939414972290600883575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87963919219963054134511433 65972939414972290600883575)
  ·
    refine ⟨98959409122458435901325363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65972939414972290600883575 98959409122458435901325363)
    ·
      refine ⟨148439113683687653851988045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98959409122458435901325363 148439113683687653851988045)
      ·
        refine ⟨55664667631382870194495517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148439113683687653851988045 55664667631382870194495517)
        ·
          refine ⟨20874250361768576322935819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55664667631382870194495517 20874250361768576322935819)
          ·
            refine ⟨31311375542652864484403729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20874250361768576322935819 31311375542652864484403729)
            ·
              refine ⟨23483531656989648363302797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31311375542652864484403729 23483531656989648363302797)
              ·
                refine ⟨8806324371371118136238549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23483531656989648363302797 8806324371371118136238549)
                ·
                  refine ⟨206398227454010581318091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8806324371371118136238549 206398227454010581318091)
                  ·
                    rfl

theorem cell23_3617632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_3617632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617632 prefixEnd_3617632 := by exact prefixLift 3617632
  have htrace : WordTrace (prefixWord ++ tailWord_3617632) baseStart_3617632 baseEnd_3617632 := by
    simpa [prefixWord, tailWord_3617632, baseEnd_3617632] using wordTrace_append hprefix tailTrace_3617632
  have hstable : (prefixWord ++ tailWord_3617632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617632).length < 2 ^ (prefixWord ++ tailWord_3617632).sum := by decide
  have hdescent : baseEnd_3617632 < baseStart_3617632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617639 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3617639 : Nat := 118140960795 + 3617639 * 2 ^ 59
def prefixEnd_3617639 : Nat := 4983230072969 + 3 ^ 40 * 3617639 * 2
def baseEnd_3617639 : Nat := 1857587641450676704475287

theorem tailTrace_3617639 : CollatzResearch.WordTrace tailWord_3617639 prefixEnd_3617639 1857587641450676704475287 := by
  unfold tailWord_3617639
  simp only [CollatzResearch.WordTrace]
  refine ⟨131946134140919221397271971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87964089427279480931514647 131946134140919221397271971)
  ·
    refine ⟨197919201211378832095907957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131946134140919221397271971 197919201211378832095907957)
    ·
      refine ⟨18554925113566765508991371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197919201211378832095907957 18554925113566765508991371)
      ·
        refine ⟨27832387670350148263487057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18554925113566765508991371 27832387670350148263487057)
        ·
          refine ⟨20874290752762611197615293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27832387670350148263487057 20874290752762611197615293)
          ·
            refine ⟨7827859032285979199105735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20874290752762611197615293 7827859032285979199105735)
            ·
              refine ⟨11741788548428968798658603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827859032285979199105735 11741788548428968798658603)
              ·
                refine ⟨17612682822643453197987905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741788548428968798658603 17612682822643453197987905)
                ·
                  refine ⟨13209512116982589898490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17612682822643453197987905 13209512116982589898490929)
                  ·
                    refine ⟨9907134087736942423868197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13209512116982589898490929 9907134087736942423868197)
                    ·
                      refine ⟨1857587641450676704475287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9907134087736942423868197 1857587641450676704475287)
                      ·
                        rfl

theorem cell23_3617639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3617639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617639 prefixEnd_3617639 := by exact prefixLift 3617639
  have htrace : WordTrace (prefixWord ++ tailWord_3617639) baseStart_3617639 baseEnd_3617639 := by
    simpa [prefixWord, tailWord_3617639, baseEnd_3617639] using wordTrace_append hprefix tailTrace_3617639
  have hstable : (prefixWord ++ tailWord_3617639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617639).length < 2 ^ (prefixWord ++ tailWord_3617639).sum := by decide
  have hdescent : baseEnd_3617639 < baseStart_3617639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617719 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_3617719 : Nat := 118140960795 + 3617719 * 2 ^ 59
def prefixEnd_3617719 : Nat := 4983230072969 + 3 ^ 40 * 3617719 * 2
def baseEnd_3617719 : Nat := 1857628719903036391474919

theorem tailTrace_3617719 : CollatzResearch.WordTrace tailWord_3617719 prefixEnd_3617719 1857628719903036391474919 := by
  unfold tailWord_3617719
  simp only [CollatzResearch.WordTrace]
  refine ⟨131949051980629395060184211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87966034653752930040122807 131949051980629395060184211)
  ·
    refine ⟨197923577970944092590276317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131949051980629395060184211 197923577970944092590276317)
    ·
      refine ⟨74221341739104034721353619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197923577970944092590276317 74221341739104034721353619)
      ·
        refine ⟨111332012608656052082030429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74221341739104034721353619 111332012608656052082030429)
        ·
          refine ⟨41749504728246019530761411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111332012608656052082030429 41749504728246019530761411)
          ·
            refine ⟨62624257092369029296142117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41749504728246019530761411 62624257092369029296142117)
            ·
              refine ⟨11742048204819192993026647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62624257092369029296142117 11742048204819192993026647)
              ·
                refine ⟨17613072307228789489539971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742048204819192993026647 17613072307228789489539971)
                ·
                  refine ⟨26419608460843184234309957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17613072307228789489539971 26419608460843184234309957)
                  ·
                    refine ⟨4953676586408097043933117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26419608460843184234309957 4953676586408097043933117)
                    ·
                      refine ⟨1857628719903036391474919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953676586408097043933117 1857628719903036391474919)
                      ·
                        rfl

theorem cell23_3617719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_3617719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617719 prefixEnd_3617719 := by exact prefixLift 3617719
  have htrace : WordTrace (prefixWord ++ tailWord_3617719) baseStart_3617719 baseEnd_3617719 := by
    simpa [prefixWord, tailWord_3617719, baseEnd_3617719] using wordTrace_append hprefix tailTrace_3617719
  have hstable : (prefixWord ++ tailWord_3617719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617719).length < 2 ^ (prefixWord ++ tailWord_3617719).sum := by decide
  have hdescent : baseEnd_3617719 < baseStart_3617719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617722 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_3617722 : Nat := 118140960795 + 3617722 * 2 ^ 59
def prefixEnd_3617722 : Nat := 4983230072969 + 3 ^ 40 * 3617722 * 2
def baseEnd_3617722 : Nat := 206403362260555542193045

theorem tailTrace_3617722 : CollatzResearch.WordTrace tailWord_3617722 prefixEnd_3617722 206403362260555542193045 := by
  unfold tailWord_3617722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32987290349904631643135855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87966107599745684381695613 32987290349904631643135855)
  ·
    refine ⟨49480935524856947464703783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32987290349904631643135855 49480935524856947464703783)
    ·
      refine ⟨74221403287285421197055675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49480935524856947464703783 74221403287285421197055675)
      ·
        refine ⟨111332104930928131795583513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74221403287285421197055675 111332104930928131795583513)
        ·
          refine ⟨83499078698196098846687635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111332104930928131795583513 83499078698196098846687635)
          ·
            refine ⟨125248618047294148270031453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83499078698196098846687635 125248618047294148270031453)
            ·
              refine ⟨46968231767735305601261795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125248618047294148270031453 46968231767735305601261795)
              ·
                refine ⟨70452347651602958401892693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46968231767735305601261795 70452347651602958401892693)
                ·
                  refine ⟨206403362260555542193045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70452347651602958401892693 206403362260555542193045)
                  ·
                    rfl

theorem cell23_3617722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_3617722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617722 prefixEnd_3617722 := by exact prefixLift 3617722
  have htrace : WordTrace (prefixWord ++ tailWord_3617722) baseStart_3617722 baseEnd_3617722 := by
    simpa [prefixWord, tailWord_3617722, baseEnd_3617722] using wordTrace_append hprefix tailTrace_3617722
  have hstable : (prefixWord ++ tailWord_3617722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617722).length < 2 ^ (prefixWord ++ tailWord_3617722).sum := by decide
  have hdescent : baseEnd_3617722 < baseStart_3617722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617734 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_3617734 : Nat := 118140960795 + 3617734 * 2 ^ 59
def prefixEnd_3617734 : Nat := 4983230072969 + 3 ^ 40 * 3617734 * 2
def baseEnd_3617734 : Nat := 206404046901428203643039

theorem tailTrace_3617734 : CollatzResearch.WordTrace tailWord_3617734 prefixEnd_3617734 206404046901428203643039 := by
  unfold tailWord_3617734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123424971111720394436883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87966399383716701747986837 4123424971111720394436883)
  ·
    refine ⟨6185137456667580591655325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4123424971111720394436883 6185137456667580591655325)
    ·
      refine ⟨2319426546250342721870747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6185137456667580591655325 2319426546250342721870747)
      ·
        refine ⟨3479139819375514082806121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319426546250342721870747 3479139819375514082806121)
        ·
          refine ⟨2609354864531635562104591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479139819375514082806121 2609354864531635562104591)
          ·
            refine ⟨3914032296797453343156887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609354864531635562104591 3914032296797453343156887)
            ·
              refine ⟨5871048445196180014735331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914032296797453343156887 5871048445196180014735331)
              ·
                refine ⟨8806572667794270022102997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871048445196180014735331 8806572667794270022102997)
                ·
                  refine ⟨206404046901428203643039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8806572667794270022102997 206404046901428203643039)
                  ·
                    rfl

theorem cell23_3617734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_3617734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617734 prefixEnd_3617734 := by exact prefixLift 3617734
  have htrace : WordTrace (prefixWord ++ tailWord_3617734) baseStart_3617734 baseEnd_3617734 := by
    simpa [prefixWord, tailWord_3617734, baseEnd_3617734] using wordTrace_append hprefix tailTrace_3617734
  have hstable : (prefixWord ++ tailWord_3617734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617734).length < 2 ^ (prefixWord ++ tailWord_3617734).sum := by decide
  have hdescent : baseEnd_3617734 < baseStart_3617734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617793 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_3617793 : Nat := 118140960795 + 3617793 * 2 ^ 59
def prefixEnd_3617793 : Nat := 4983230072969 + 3 ^ 40 * 3617793 * 2
def baseEnd_3617793 : Nat := 1857666717471469101949579

theorem tailTrace_3617793 : CollatzResearch.WordTrace tailWord_3617793 prefixEnd_3617793 1857666717471469101949579 := by
  unfold tailWord_3617793
  simp only [CollatzResearch.WordTrace]
  refine ⟨131951750982361305698378033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87967833988240870465585355 131951750982361305698378033)
  ·
    refine ⟨98963813236770979273783525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131951750982361305698378033 98963813236770979273783525)
    ·
      refine ⟨18555714981894558613834411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98963813236770979273783525 18555714981894558613834411)
      ·
        refine ⟨27833572472841837920751617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18555714981894558613834411 27833572472841837920751617)
        ·
          refine ⟨20875179354631378440563713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27833572472841837920751617 20875179354631378440563713)
          ·
            refine ⟨15656384515973533830422785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20875179354631378440563713 15656384515973533830422785)
            ·
              refine ⟨11742288386980150372817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15656384515973533830422785 11742288386980150372817089)
              ·
                refine ⟨8806716290235112779612817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11742288386980150372817089 8806716290235112779612817)
                ·
                  refine ⟨6605037217676334584709613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8806716290235112779612817 6605037217676334584709613)
                  ·
                    refine ⟨2476888956628625469266105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6605037217676334584709613 2476888956628625469266105)
                    ·
                      refine ⟨1857666717471469101949579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476888956628625469266105 1857666717471469101949579)
                      ·
                        rfl

theorem cell23_3617793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_3617793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617793 prefixEnd_3617793 := by exact prefixLift 3617793
  have htrace : WordTrace (prefixWord ++ tailWord_3617793) baseStart_3617793 baseEnd_3617793 := by
    simpa [prefixWord, tailWord_3617793, baseEnd_3617793] using wordTrace_append hprefix tailTrace_3617793
  have hstable : (prefixWord ++ tailWord_3617793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617793).length < 2 ^ (prefixWord ++ tailWord_3617793).sum := by decide
  have hdescent : baseEnd_3617793 < baseStart_3617793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617799 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3617799 : Nat := 118140960795 + 3617799 * 2 ^ 59
def prefixEnd_3617799 : Nat := 4983230072969 + 3 ^ 40 * 3617799 * 2
def baseEnd_3617799 : Nat := 619223266118465359491517

theorem tailTrace_3617799 : CollatzResearch.WordTrace tailWord_3617799 prefixEnd_3617799 619223266118465359491517 := by
  unfold tailWord_3617799
  simp only [CollatzResearch.WordTrace]
  refine ⟨131951969820339568723096451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87967979880226379148730967 131951969820339568723096451)
  ·
    refine ⟨197927954730509353084644677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131951969820339568723096451 197927954730509353084644677)
    ·
      refine ⟨37111491511970503703370877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197927954730509353084644677 37111491511970503703370877)
      ·
        refine ⟨13916809316988938888764079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37111491511970503703370877 13916809316988938888764079)
        ·
          refine ⟨20875213975483408333146119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13916809316988938888764079 20875213975483408333146119)
          ·
            refine ⟨31312820963225112499719179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20875213975483408333146119 31312820963225112499719179)
            ·
              refine ⟨46969231444837668749578769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31312820963225112499719179 46969231444837668749578769)
              ·
                refine ⟨35226923583628251562184077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46969231444837668749578769 35226923583628251562184077)
                ·
                  refine ⟨13210096343860594335819029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35226923583628251562184077 13210096343860594335819029)
                  ·
                    refine ⟨619223266118465359491517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13210096343860594335819029 619223266118465359491517)
                    ·
                      rfl

theorem cell23_3617799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3617799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617799 prefixEnd_3617799 := by exact prefixLift 3617799
  have htrace : WordTrace (prefixWord ++ tailWord_3617799) baseStart_3617799 baseEnd_3617799 := by
    simpa [prefixWord, tailWord_3617799, baseEnd_3617799] using wordTrace_append hprefix tailTrace_3617799
  have hstable : (prefixWord ++ tailWord_3617799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617799).length < 2 ^ (prefixWord ++ tailWord_3617799).sum := by decide
  have hdescent : baseEnd_3617799 < baseStart_3617799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617800 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_3617800 : Nat := 118140960795 + 3617800 * 2 ^ 59
def prefixEnd_3617800 : Nat := 4983230072969 + 3 ^ 40 * 3617800 * 2
def baseEnd_3617800 : Nat := 1857670311836050574562047

theorem tailTrace_3617800 : CollatzResearch.WordTrace tailWord_3617800 prefixEnd_3617800 1857670311836050574562047 := by
  unfold tailWord_3617800
  simp only [CollatzResearch.WordTrace]
  refine ⟨65976003146667972946941427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87968004195557297262588569 65976003146667972946941427)
  ·
    refine ⟨98964004720001959420412141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65976003146667972946941427 98964004720001959420412141)
    ·
      refine ⟨37111501770000734782654553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98964004720001959420412141 37111501770000734782654553)
      ·
        refine ⟨27833626327500551086990915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37111501770000734782654553 27833626327500551086990915)
        ·
          refine ⟨41750439491250826630486373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27833626327500551086990915 41750439491250826630486373)
          ·
            refine ⟨7828207404609529993216195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41750439491250826630486373 7828207404609529993216195)
            ·
              refine ⟨11742311106914294989824293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828207404609529993216195 11742311106914294989824293)
              ·
                refine ⟨2201683332546430310592055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11742311106914294989824293 2201683332546430310592055)
                ·
                  refine ⟨3302524998819645465888083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201683332546430310592055 3302524998819645465888083)
                  ·
                    refine ⟨4953787498229468198832125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302524998819645465888083 4953787498229468198832125)
                    ·
                      refine ⟨1857670311836050574562047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953787498229468198832125 1857670311836050574562047)
                      ·
                        rfl

theorem cell23_3617800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_3617800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617800 prefixEnd_3617800 := by exact prefixLift 3617800
  have htrace : WordTrace (prefixWord ++ tailWord_3617800) baseStart_3617800 baseEnd_3617800 := by
    simpa [prefixWord, tailWord_3617800, baseEnd_3617800] using wordTrace_append hprefix tailTrace_3617800
  have hstable : (prefixWord ++ tailWord_3617800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617800).length < 2 ^ (prefixWord ++ tailWord_3617800).sum := by decide
  have hdescent : baseEnd_3617800 < baseStart_3617800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617806 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3617806 : Nat := 118140960795 + 3617806 * 2 ^ 59
def prefixEnd_3617806 : Nat := 4983230072969 + 3 ^ 40 * 3617806 * 2
def baseEnd_3617806 : Nat := 1857673392719977551087019

theorem tailTrace_3617806 : CollatzResearch.WordTrace tailWord_3617806 prefixEnd_3617806 1857673392719977551087019 := by
  unfold tailWord_3617806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494028141414276114825159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87968150087542805945734181 16494028141414276114825159)
  ·
    refine ⟨24741042212121414172237739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16494028141414276114825159 24741042212121414172237739)
    ·
      refine ⟨37111563318182121258356609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24741042212121414172237739 37111563318182121258356609)
      ·
        refine ⟨27833672488636590943767457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37111563318182121258356609 27833672488636590943767457)
        ·
          refine ⟨20875254366477443207825593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27833672488636590943767457 20875254366477443207825593)
          ·
            refine ⟨15656440774858082405869195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20875254366477443207825593 15656440774858082405869195)
            ·
              refine ⟨23484661162287123608803793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656440774858082405869195 23484661162287123608803793)
              ·
                refine ⟨17613495871715342706602845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23484661162287123608803793 17613495871715342706602845)
                ·
                  refine ⟨6605060951893253514976067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17613495871715342706602845 6605060951893253514976067)
                  ·
                    refine ⟨9907591427839880272464101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6605060951893253514976067 9907591427839880272464101)
                    ·
                      refine ⟨1857673392719977551087019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9907591427839880272464101 1857673392719977551087019)
                      ·
                        rfl

theorem cell23_3617806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3617806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617806 prefixEnd_3617806 := by exact prefixLift 3617806
  have htrace : WordTrace (prefixWord ++ tailWord_3617806) baseStart_3617806 baseEnd_3617806 := by
    simpa [prefixWord, tailWord_3617806, baseEnd_3617806] using wordTrace_append hprefix tailTrace_3617806
  have hstable : (prefixWord ++ tailWord_3617806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617806).length < 2 ^ (prefixWord ++ tailWord_3617806).sum := by decide
  have hdescent : baseEnd_3617806 < baseStart_3617806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3617809 : Nat := 118140960795 + 3617809 * 2 ^ 59
def prefixEnd_3617809 : Nat := 4983230072969 + 3 ^ 40 * 3617809 * 2
def baseEnd_3617809 : Nat := 1857674933161941039349505

theorem tailTrace_3617809 : CollatzResearch.WordTrace tailWord_3617809 prefixEnd_3617809 1857674933161941039349505 := by
  unfold tailWord_3617809
  simp only [CollatzResearch.WordTrace]
  refine ⟨131952334550303340430960481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87968223033535560287306987 131952334550303340430960481)
  ·
    refine ⟨98964250912727505323220361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131952334550303340430960481 98964250912727505323220361)
    ·
      refine ⟨74223188184545628992415271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98964250912727505323220361 74223188184545628992415271)
      ·
        refine ⟨111334782276818443488622907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74223188184545628992415271 111334782276818443488622907)
        ·
          refine ⟨167002173415227665232934361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111334782276818443488622907 167002173415227665232934361)
          ·
            refine ⟨125251630061420748924700771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167002173415227665232934361 125251630061420748924700771)
            ·
              refine ⟨187877445092131123387051157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125251630061420748924700771 187877445092131123387051157)
              ·
                refine ⟨8806755238693646408768023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187877445092131123387051157 8806755238693646408768023)
                ·
                  refine ⟨13210132858040469613152035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806755238693646408768023 13210132858040469613152035)
                  ·
                    refine ⟨19815199287060704419728053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13210132858040469613152035 19815199287060704419728053)
                    ·
                      refine ⟨1857674933161941039349505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19815199287060704419728053 1857674933161941039349505)
                      ·
                        rfl

theorem cell23_3617809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3617809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617809 prefixEnd_3617809 := by exact prefixLift 3617809
  have htrace : WordTrace (prefixWord ++ tailWord_3617809) baseStart_3617809 baseEnd_3617809 := by
    simpa [prefixWord, tailWord_3617809, baseEnd_3617809] using wordTrace_append hprefix tailTrace_3617809
  have hstable : (prefixWord ++ tailWord_3617809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617809).length < 2 ^ (prefixWord ++ tailWord_3617809).sum := by decide
  have hdescent : baseEnd_3617809 < baseStart_3617809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617816 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_3617816 : Nat := 118140960795 + 3617816 * 2 ^ 59
def prefixEnd_3617816 : Nat := 4983230072969 + 3 ^ 40 * 3617816 * 2
def baseEnd_3617816 : Nat := 619226175842174170653991

theorem tailTrace_3617816 : CollatzResearch.WordTrace tailWord_3617816 prefixEnd_3617816 619226175842174170653991 := by
  unfold tailWord_3617816
  simp only [CollatzResearch.WordTrace]
  refine ⟨65976294930638990313232651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87968393240851987084310201 65976294930638990313232651)
  ·
    refine ⟨98964442395958485469848977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65976294930638990313232651 98964442395958485469848977)
    ·
      refine ⟨74223331796968864102386733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98964442395958485469848977 74223331796968864102386733)
      ·
        refine ⟨27833749423863324038395025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74223331796968864102386733 27833749423863324038395025)
        ·
          refine ⟨20875312067897493028796269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27833749423863324038395025 20875312067897493028796269)
          ·
            refine ⟨7828242025461559885798601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20875312067897493028796269 7828242025461559885798601)
            ·
              refine ⟨5871181519096169914348951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828242025461559885798601 5871181519096169914348951)
              ·
                refine ⟨8806772278644254871523427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871181519096169914348951 8806772278644254871523427)
                ·
                  refine ⟨13210158417966382307285141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806772278644254871523427 13210158417966382307285141)
                  ·
                    refine ⟨619226175842174170653991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13210158417966382307285141 619226175842174170653991)
                    ·
                      rfl

theorem cell23_3617816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_3617816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617816 prefixEnd_3617816 := by exact prefixLift 3617816
  have htrace : WordTrace (prefixWord ++ tailWord_3617816) baseStart_3617816 baseEnd_3617816 := by
    simpa [prefixWord, tailWord_3617816, baseEnd_3617816] using wordTrace_append hprefix tailTrace_3617816
  have hstable : (prefixWord ++ tailWord_3617816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617816).length < 2 ^ (prefixWord ++ tailWord_3617816).sum := by decide
  have hdescent : baseEnd_3617816 < baseStart_3617816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617823 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 5, 2, 2]
def baseStart_3617823 : Nat := 118140960795 + 3617823 * 2 ^ 59
def prefixEnd_3617823 : Nat := 4983230072969 + 3 ^ 40 * 3617823 * 2
def baseEnd_3617823 : Nat := 1857682121891103984574441

theorem tailTrace_3617823 : CollatzResearch.WordTrace tailWord_3617823 prefixEnd_3617823 1857682121891103984574441 := by
  unfold tailWord_3617823
  simp only [CollatzResearch.WordTrace]
  refine ⟨131952845172252620821970123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87968563448168413881313415 131952845172252620821970123)
  ·
    refine ⟨197929267758378931232955185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131952845172252620821970123 197929267758378931232955185)
    ·
      refine ⟨148446950818784198424716389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197929267758378931232955185 148446950818784198424716389)
      ·
        refine ⟨27833803278522037204634323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148446950818784198424716389 27833803278522037204634323)
        ·
          refine ⟨41750704917783055806951485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27833803278522037204634323 41750704917783055806951485)
          ·
            refine ⟨15656514344168645927606807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41750704917783055806951485 15656514344168645927606807)
            ·
              refine ⟨23484771516252968891410211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656514344168645927606807 23484771516252968891410211)
              ·
                refine ⟨35227157274379453337115317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23484771516252968891410211 35227157274379453337115317)
                ·
                  refine ⟨3302545994473073750354561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35227157274379453337115317 3302545994473073750354561)
                  ·
                    refine ⟨2476909495854805312765921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302545994473073750354561 2476909495854805312765921)
                    ·
                      refine ⟨1857682121891103984574441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476909495854805312765921 1857682121891103984574441)
                      ·
                        rfl

theorem cell23_3617823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_3617823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617823 prefixEnd_3617823 := by exact prefixLift 3617823
  have htrace : WordTrace (prefixWord ++ tailWord_3617823) baseStart_3617823 baseEnd_3617823 := by
    simpa [prefixWord, tailWord_3617823, baseEnd_3617823] using wordTrace_append hprefix tailTrace_3617823
  have hstable : (prefixWord ++ tailWord_3617823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617823).length < 2 ^ (prefixWord ++ tailWord_3617823).sum := by decide
  have hdescent : baseEnd_3617823 < baseStart_3617823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617839 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_3617839 : Nat := 118140960795 + 3617839 * 2 ^ 59
def prefixEnd_3617839 : Nat := 4983230072969 + 3 ^ 40 * 3617839 * 2
def baseEnd_3617839 : Nat := 1857690337581575921974367

theorem tailTrace_3617839 : CollatzResearch.WordTrace tailWord_3617839 prefixEnd_3617839 1857690337581575921974367 := by
  unfold tailWord_3617839
  simp only [CollatzResearch.WordTrace]
  refine ⟨131953428740194655554552571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87968952493463103703035047 131953428740194655554552571)
  ·
    refine ⟨197930143110291983331828857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131953428740194655554552571 197930143110291983331828857)
    ·
      refine ⟨148447607332718987498871643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197930143110291983331828857 148447607332718987498871643)
      ·
        refine ⟨222671410999078481248307465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148447607332718987498871643 222671410999078481248307465)
        ·
          refine ⟨167003558249308860936230599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222671410999078481248307465 167003558249308860936230599)
          ·
            refine ⟨250505337373963291404345899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167003558249308860936230599 250505337373963291404345899)
            ·
              refine ⟨375758006060944937106518849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250505337373963291404345899 375758006060944937106518849)
              ·
                refine ⟨281818504545708702829889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375758006060944937106518849 281818504545708702829889137)
                ·
                  refine ⟨211363878409281527122416853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281818504545708702829889137 211363878409281527122416853)
                  ·
                    refine ⟨4953840900217535791931645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211363878409281527122416853 4953840900217535791931645)
                    ·
                      refine ⟨1857690337581575921974367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953840900217535791931645 1857690337581575921974367)
                      ·
                        rfl

theorem cell23_3617839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_3617839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617839 prefixEnd_3617839 := by exact prefixLift 3617839
  have htrace : WordTrace (prefixWord ++ tailWord_3617839) baseStart_3617839 baseEnd_3617839 := by
    simpa [prefixWord, tailWord_3617839, baseEnd_3617839] using wordTrace_append hprefix tailTrace_3617839
  have hstable : (prefixWord ++ tailWord_3617839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617839).length < 2 ^ (prefixWord ++ tailWord_3617839).sum := by decide
  have hdescent : baseEnd_3617839 < baseStart_3617839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617846 : List Nat := [5, 1, 2, 1, 1, 3, 10]
def baseStart_3617846 : Nat := 118140960795 + 3617846 * 2 ^ 59
def prefixEnd_3617846 : Nat := 4983230072969 + 3 ^ 40 * 3617846 * 2
def baseEnd_3617846 : Nat := 22934492986989597464035

theorem tailTrace_3617846 : CollatzResearch.WordTrace tailWord_3617846 prefixEnd_3617846 22934492986989597464035 := by
  unfold tailWord_3617846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247105253198080984378587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87969122700779530500038261 8247105253198080984378587)
  ·
    refine ⟨12370657879797121476567881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8247105253198080984378587 12370657879797121476567881)
    ·
      refine ⟨9277993409847841107425911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12370657879797121476567881 9277993409847841107425911)
      ·
        refine ⟨13916990114771761661138867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277993409847841107425911 13916990114771761661138867)
        ·
          refine ⟨20875485172157642491708301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13916990114771761661138867 20875485172157642491708301)
          ·
            refine ⟨7828306939559115934390613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20875485172157642491708301 7828306939559115934390613)
            ·
              refine ⟨22934492986989597464035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7828306939559115934390613 22934492986989597464035)
              ·
                rfl

theorem cell23_3617846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 10].length) (baseStart_3617846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617846 prefixEnd_3617846 := by exact prefixLift 3617846
  have htrace : WordTrace (prefixWord ++ tailWord_3617846) baseStart_3617846 baseEnd_3617846 := by
    simpa [prefixWord, tailWord_3617846, baseEnd_3617846] using wordTrace_append hprefix tailTrace_3617846
  have hstable : (prefixWord ++ tailWord_3617846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617846).length < 2 ^ (prefixWord ++ tailWord_3617846).sum := by decide
  have hdescent : baseEnd_3617846 < baseStart_3617846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617857 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3617857 : Nat := 118140960795 + 3617857 * 2 ^ 59
def prefixEnd_3617857 : Nat := 4983230072969 + 3 ^ 40 * 3617857 * 2
def baseEnd_3617857 : Nat := 1857699580233356851549285

theorem tailTrace_3617857 : CollatzResearch.WordTrace tailWord_3617857 prefixEnd_3617857 1857699580233356851549285 := by
  unfold tailWord_3617857
  simp only [CollatzResearch.WordTrace]
  refine ⟨131954085254129444628707825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87969390169419629752471883 131954085254129444628707825)
  ·
    refine ⟨98965563940597083471530869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131954085254129444628707825 98965563940597083471530869)
    ·
      refine ⟨9278021619430976575456019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98965563940597083471530869 9278021619430976575456019)
      ·
        refine ⟨13917032429146464863184029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9278021619430976575456019 13917032429146464863184029)
        ·
          refine ⟨5218887160929924323694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13917032429146464863184029 5218887160929924323694011)
          ·
            refine ⟨7828330741394886485541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218887160929924323694011 7828330741394886485541017)
            ·
              refine ⟨5871248056046164864155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828330741394886485541017 5871248056046164864155763)
              ·
                refine ⟨8806872084069247296233645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871248056046164864155763 8806872084069247296233645)
                ·
                  refine ⟨3302577031525967736087617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8806872084069247296233645 3302577031525967736087617)
                  ·
                    refine ⟨2476932773644475802065713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302577031525967736087617 2476932773644475802065713)
                    ·
                      refine ⟨1857699580233356851549285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2476932773644475802065713 1857699580233356851549285)
                      ·
                        rfl

theorem cell23_3617857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3617857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617857 prefixEnd_3617857 := by exact prefixLift 3617857
  have htrace : WordTrace (prefixWord ++ tailWord_3617857) baseStart_3617857 baseEnd_3617857 := by
    simpa [prefixWord, tailWord_3617857, baseEnd_3617857] using wordTrace_append hprefix tailTrace_3617857
  have hstable : (prefixWord ++ tailWord_3617857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617857).length < 2 ^ (prefixWord ++ tailWord_3617857).sum := by decide
  have hdescent : baseEnd_3617857 < baseStart_3617857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617873 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_3617873 : Nat := 118140960795 + 3617873 * 2 ^ 59
def prefixEnd_3617873 : Nat := 4983230072969 + 3 ^ 40 * 3617873 * 2
def baseEnd_3617873 : Nat := 1857707795923828788949211

theorem tailTrace_3617873 : CollatzResearch.WordTrace tailWord_3617873 prefixEnd_3617873 1857707795923828788949211 := by
  unfold tailWord_3617873
  simp only [CollatzResearch.WordTrace]
  refine ⟨131954668822071479361290273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87969779214714319574193515 131954668822071479361290273)
  ·
    refine ⟨98966001616553609520967705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131954668822071479361290273 98966001616553609520967705)
    ·
      refine ⟨74224501212415207140725779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98966001616553609520967705 74224501212415207140725779)
      ·
        refine ⟨111336751818622810711088669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74224501212415207140725779 111336751818622810711088669)
        ·
          refine ⟨41751281931983554016658251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111336751818622810711088669 41751281931983554016658251)
          ·
            refine ⟨62626922897975331024987377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41751281931983554016658251 62626922897975331024987377)
            ·
              refine ⟨46970192173481498268740533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62626922897975331024987377 46970192173481498268740533)
              ·
                refine ⟨4403455516263890462694425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46970192173481498268740533 4403455516263890462694425)
                ·
                  refine ⟨3302591637197917847020819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4403455516263890462694425 3302591637197917847020819)
                  ·
                    refine ⟨4953887455796876770531229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302591637197917847020819 4953887455796876770531229)
                    ·
                      refine ⟨1857707795923828788949211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953887455796876770531229 1857707795923828788949211)
                      ·
                        rfl

theorem cell23_3617873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_3617873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617873 prefixEnd_3617873 := by exact prefixLift 3617873
  have htrace : WordTrace (prefixWord ++ tailWord_3617873) baseStart_3617873 baseEnd_3617873 := by
    simpa [prefixWord, tailWord_3617873, baseEnd_3617873] using wordTrace_append hprefix tailTrace_3617873
  have hstable : (prefixWord ++ tailWord_3617873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617873).length < 2 ^ (prefixWord ++ tailWord_3617873).sum := by decide
  have hdescent : baseEnd_3617873 < baseStart_3617873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617889 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3617889 : Nat := 118140960795 + 3617889 * 2 ^ 59
def prefixEnd_3617889 : Nat := 4983230072969 + 3 ^ 40 * 3617889 * 2
def baseEnd_3617889 : Nat := 619238670538100242116379

theorem tailTrace_3617889 : CollatzResearch.WordTrace tailWord_3617889 prefixEnd_3617889 619238670538100242116379 := by
  unfold tailWord_3617889
  simp only [CollatzResearch.WordTrace]
  refine ⟨131955252390013514093872721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87970168260009009395915147 131955252390013514093872721)
  ·
    refine ⟨98966439292510135570404541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131955252390013514093872721 98966439292510135570404541)
    ·
      refine ⟨37112414734691300838901703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98966439292510135570404541 37112414734691300838901703)
      ·
        refine ⟨55668622102036951258352555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37112414734691300838901703 55668622102036951258352555)
        ·
          refine ⟨83502933153055426887528833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55668622102036951258352555 83502933153055426887528833)
          ·
            refine ⟨62627199864791570165646625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83502933153055426887528833 62627199864791570165646625)
            ·
              refine ⟨46970399898593677624234969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62627199864791570165646625 46970399898593677624234969)
              ·
                refine ⟨35227799923945258218176227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46970399898593677624234969 35227799923945258218176227)
                ·
                  refine ⟨52841699885917887327264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35227799923945258218176227 52841699885917887327264341)
                  ·
                    refine ⟨619238670538100242116379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52841699885917887327264341 619238670538100242116379)
                    ·
                      rfl

theorem cell23_3617889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3617889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617889 prefixEnd_3617889 := by exact prefixLift 3617889
  have htrace : WordTrace (prefixWord ++ tailWord_3617889) baseStart_3617889 baseEnd_3617889 := by
    simpa [prefixWord, tailWord_3617889, baseEnd_3617889] using wordTrace_append hprefix tailTrace_3617889
  have hstable : (prefixWord ++ tailWord_3617889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617889).length < 2 ^ (prefixWord ++ tailWord_3617889).sum := by decide
  have hdescent : baseEnd_3617889 < baseStart_3617889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617890 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3617890 : Nat := 118140960795 + 3617890 * 2 ^ 59
def prefixEnd_3617890 : Nat := 4983230072969 + 3 ^ 40 * 3617890 * 2
def baseEnd_3617890 : Nat := 1857716525094955222436633

theorem tailTrace_3617890 : CollatzResearch.WordTrace tailWord_3617890 prefixEnd_3617890 1857716525094955222436633 := by
  unfold tailWord_3617890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32988822215752472816164781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87970192575339927509772749 32988822215752472816164781)
  ·
    refine ⟨12370808330907177306061793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32988822215752472816164781 12370808330907177306061793)
    ·
      refine ⟨9278106248180382979546345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12370808330907177306061793 9278106248180382979546345)
      ·
        refine ⟨6958579686135287234659759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278106248180382979546345 6958579686135287234659759)
        ·
          refine ⟨10437869529202930851989639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958579686135287234659759 10437869529202930851989639)
          ·
            refine ⟨15656804293804396277984459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437869529202930851989639 15656804293804396277984459)
            ·
              refine ⟨23485206440706594416976689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656804293804396277984459 23485206440706594416976689)
              ·
                refine ⟨17613904830529945812732517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23485206440706594416976689 17613904830529945812732517)
                ·
                  refine ⟨3302607155724364839887347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17613904830529945812732517 3302607155724364839887347)
                  ·
                    refine ⟨4953910733586547259831021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302607155724364839887347 4953910733586547259831021)
                    ·
                      refine ⟨1857716525094955222436633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953910733586547259831021 1857716525094955222436633)
                      ·
                        rfl

theorem cell23_3617890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3617890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617890 prefixEnd_3617890 := by exact prefixLift 3617890
  have htrace : WordTrace (prefixWord ++ tailWord_3617890) baseStart_3617890 baseEnd_3617890 := by
    simpa [prefixWord, tailWord_3617890, baseEnd_3617890] using wordTrace_append hprefix tailTrace_3617890
  have hstable : (prefixWord ++ tailWord_3617890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617890).length < 2 ^ (prefixWord ++ tailWord_3617890).sum := by decide
  have hdescent : baseEnd_3617890 < baseStart_3617890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617916 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3617916 : Nat := 118140960795 + 3617916 * 2 ^ 59
def prefixEnd_3617916 : Nat := 4983230072969 + 3 ^ 40 * 3617916 * 2
def baseEnd_3617916 : Nat := 1857729875591972120711513

theorem tailTrace_3617916 : CollatzResearch.WordTrace tailWord_3617916 prefixEnd_3617916 1857729875591972120711513 := by
  unfold tailWord_3617916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65978118580457848852552801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87970824773943798470070401 65978118580457848852552801)
  ·
    refine ⟨49483588935343386639414601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65978118580457848852552801 49483588935343386639414601)
    ·
      refine ⟨37112691701507539979560951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49483588935343386639414601 37112691701507539979560951)
      ·
        refine ⟨55669037552261309969341427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37112691701507539979560951 55669037552261309969341427)
        ·
          refine ⟨83503556328391964954012141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55669037552261309969341427 83503556328391964954012141)
          ·
            refine ⟨31313833623146986857754553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83503556328391964954012141 31313833623146986857754553)
            ·
              refine ⟨23485375217360240143315915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31313833623146986857754553 23485375217360240143315915)
              ·
                refine ⟨35228062826040360214973873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485375217360240143315915 35228062826040360214973873)
                ·
                  refine ⟨26421047119530270161230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35228062826040360214973873 26421047119530270161230405)
                  ·
                    refine ⟨4953946334911925655230701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26421047119530270161230405 4953946334911925655230701)
                    ·
                      refine ⟨1857729875591972120711513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4953946334911925655230701 1857729875591972120711513)
                      ·
                        rfl

theorem cell23_3617916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3617916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617916 prefixEnd_3617916 := by exact prefixLift 3617916
  have htrace : WordTrace (prefixWord ++ tailWord_3617916) baseStart_3617916 baseEnd_3617916 := by
    simpa [prefixWord, tailWord_3617916, baseEnd_3617916] using wordTrace_append hprefix tailTrace_3617916
  have hstable : (prefixWord ++ tailWord_3617916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617916).length < 2 ^ (prefixWord ++ tailWord_3617916).sum := by decide
  have hdescent : baseEnd_3617916 < baseStart_3617916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617918 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3617918 : Nat := 118140960795 + 3617918 * 2 ^ 59
def prefixEnd_3617918 : Nat := 4983230072969 + 3 ^ 40 * 3617918 * 2
def baseEnd_3617918 : Nat := 619243634184427037628835

theorem tailTrace_3617918 : CollatzResearch.WordTrace tailWord_3617918 prefixEnd_3617918 619243634184427037628835 := by
  unfold tailWord_3617918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494538763363556505834801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87970873404605634697785605 16494538763363556505834801)
  ·
    refine ⟨12370904072522667379376101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16494538763363556505834801 12370904072522667379376101)
    ·
      refine ⟨2319544513598000133633019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12370904072522667379376101 2319544513598000133633019)
      ·
        refine ⟨3479316770397000200449529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319544513598000133633019 3479316770397000200449529)
        ·
          refine ⟨2609487577797750150337147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479316770397000200449529 2609487577797750150337147)
          ·
            refine ⟨3914231366696625225505721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609487577797750150337147 3914231366696625225505721)
            ·
              refine ⟨2935673525022468919129291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914231366696625225505721 2935673525022468919129291)
              ·
                refine ⟨4403510287533703378693937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935673525022468919129291 4403510287533703378693937)
                ·
                  refine ⟨3302632715650277534020453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4403510287533703378693937 3302632715650277534020453)
                  ·
                    refine ⟨619243634184427037628835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3302632715650277534020453 619243634184427037628835)
                    ·
                      rfl

theorem cell23_3617918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3617918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617918 prefixEnd_3617918 := by exact prefixLift 3617918
  have htrace : WordTrace (prefixWord ++ tailWord_3617918) baseStart_3617918 baseEnd_3617918 := by
    simpa [prefixWord, tailWord_3617918, baseEnd_3617918] using wordTrace_append hprefix tailTrace_3617918
  have hstable : (prefixWord ++ tailWord_3617918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617918).length < 2 ^ (prefixWord ++ tailWord_3617918).sum := by decide
  have hdescent : baseEnd_3617918 < baseStart_3617918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617953 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 5]
def baseStart_3617953 : Nat := 118140960795 + 3617953 * 2 ^ 59
def prefixEnd_3617953 : Nat := 4983230072969 + 3 ^ 40 * 3617953 * 2
def baseEnd_3617953 : Nat := 206416541597354275105427

theorem tailTrace_3617953 : CollatzResearch.WordTrace tailWord_3617953 prefixEnd_3617953 206416541597354275105427 := by
  unfold tailWord_3617953
  simp only [CollatzResearch.WordTrace]
  refine ⟨131957586661781653024202513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87971724441187768682801675 131957586661781653024202513)
  ·
    refine ⟨98968189996336239768151885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131957586661781653024202513 98968189996336239768151885)
    ·
      refine ⟨37113071248626089913056957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98968189996336239768151885 37113071248626089913056957)
      ·
        refine ⟨13917401718234783717396359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37113071248626089913056957 13917401718234783717396359)
        ·
          refine ⟨20876102577352175576094539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13917401718234783717396359 20876102577352175576094539)
          ·
            refine ⟨31314153866028263364141809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20876102577352175576094539 31314153866028263364141809)
            ·
              refine ⟨23485615399521197523106357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31314153866028263364141809 23485615399521197523106357)
              ·
                refine ⟨2201776443705112267791221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23485615399521197523106357 2201776443705112267791221)
                ·
                  refine ⟨206416541597354275105427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201776443705112267791221 206416541597354275105427)
                  ·
                    rfl

theorem cell23_3617953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 5].length) (baseStart_3617953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617953 prefixEnd_3617953 := by exact prefixLift 3617953
  have htrace : WordTrace (prefixWord ++ tailWord_3617953) baseStart_3617953 baseEnd_3617953 := by
    simpa [prefixWord, tailWord_3617953, baseEnd_3617953] using wordTrace_append hprefix tailTrace_3617953
  have hstable : (prefixWord ++ tailWord_3617953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617953).length < 2 ^ (prefixWord ++ tailWord_3617953).sum := by decide
  have hdescent : baseEnd_3617953 < baseStart_3617953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3617970 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_3617970 : Nat := 118140960795 + 3617970 * 2 ^ 59
def prefixEnd_3617970 : Nat := 4983230072969 + 3 ^ 40 * 3617970 * 2
def baseEnd_3617970 : Nat := 206417511505257212159585

theorem tailTrace_3617970 : CollatzResearch.WordTrace tailWord_3617970 prefixEnd_3617970 206417511505257212159585 := by
  unfold tailWord_3617970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989551675680016231892841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87972137801813376618380909 32989551675680016231892841)
  ·
    refine ⟨24742163756760012173919631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32989551675680016231892841 24742163756760012173919631)
    ·
      refine ⟨37113245635140018260879447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24742163756760012173919631 37113245635140018260879447)
      ·
        refine ⟨55669868452710027391319171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37113245635140018260879447 55669868452710027391319171)
        ·
          refine ⟨83504802679065041086978757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55669868452710027391319171 83504802679065041086978757)
          ·
            refine ⟨15657150502324695203808517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83504802679065041086978757 15657150502324695203808517)
            ·
              refine ⟨2935715719185880350714097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15657150502324695203808517 2935715719185880350714097)
              ·
                refine ⟨2201786789389410263035573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935715719185880350714097 2201786789389410263035573)
                ·
                  refine ⟨206417511505257212159585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201786789389410263035573 206417511505257212159585)
                  ·
                    rfl

theorem cell23_3617970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_3617970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3617970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3617970 prefixEnd_3617970 := by exact prefixLift 3617970
  have htrace : WordTrace (prefixWord ++ tailWord_3617970) baseStart_3617970 baseEnd_3617970 := by
    simpa [prefixWord, tailWord_3617970, baseEnd_3617970] using wordTrace_append hprefix tailTrace_3617970
  have hstable : (prefixWord ++ tailWord_3617970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3617970).length < 2 ^ (prefixWord ++ tailWord_3617970).sum := by decide
  have hdescent : baseEnd_3617970 < baseStart_3617970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3617970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618016 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3618016 : Nat := 118140960795 + 3618016 * 2 ^ 59
def prefixEnd_3618016 : Nat := 4983230072969 + 3 ^ 40 * 3618016 * 2
def baseEnd_3618016 : Nat := 1857781223657421729461053

theorem tailTrace_3618016 : CollatzResearch.WordTrace tailWord_3618016 prefixEnd_3618016 1857781223657421729461053 := by
  unfold tailWord_3618016
  simp only [CollatzResearch.WordTrace]
  refine ⟨65979942230276707391872951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87973256307035609855830601 65979942230276707391872951)
  ·
    refine ⟨98969913345415061087809427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65979942230276707391872951 98969913345415061087809427)
    ·
      refine ⟨148454870018122591631714141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98969913345415061087809427 148454870018122591631714141)
      ·
        refine ⟨55670576256795971861892803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148454870018122591631714141 55670576256795971861892803)
        ·
          refine ⟨83505864385193957792839205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55670576256795971861892803 83505864385193957792839205)
          ·
            refine ⟨15657349572223867086157351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83505864385193957792839205 15657349572223867086157351)
            ·
              refine ⟨23486024358335800629236027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657349572223867086157351 23486024358335800629236027)
              ·
                refine ⟨35229036537503700943854041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23486024358335800629236027 35229036537503700943854041)
                ·
                  refine ⟨26421777403127775707890531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35229036537503700943854041 26421777403127775707890531)
                  ·
                    refine ⟨39632666104691663561835797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26421777403127775707890531 39632666104691663561835797)
                    ·
                      refine ⟨1857781223657421729461053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39632666104691663561835797 1857781223657421729461053)
                      ·
                        rfl

theorem cell23_3618016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3618016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618016 prefixEnd_3618016 := by exact prefixLift 3618016
  have htrace : WordTrace (prefixWord ++ tailWord_3618016) baseStart_3618016 baseEnd_3618016 := by
    simpa [prefixWord, tailWord_3618016, baseEnd_3618016] using wordTrace_append hprefix tailTrace_3618016
  have hstable : (prefixWord ++ tailWord_3618016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618016).length < 2 ^ (prefixWord ++ tailWord_3618016).sum := by decide
  have hdescent : baseEnd_3618016 < baseStart_3618016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618110 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3618110 : Nat := 118140960795 + 3618110 * 2 ^ 59
def prefixEnd_3618110 : Nat := 4983230072969 + 3 ^ 40 * 3618110 * 2
def baseEnd_3618110 : Nat := 1857829490838944361685621

theorem tailTrace_3618110 : CollatzResearch.WordTrace tailWord_3618110 prefixEnd_3618110 1857829490838944361685621 := by
  unfold tailWord_3618110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495414115276608604708473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87975541948141912558445189 16495414115276608604708473)
  ·
    refine ⟨12371560586457456453531355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16495414115276608604708473 12371560586457456453531355)
    ·
      refine ⟨18557340879686184680297033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371560586457456453531355 18557340879686184680297033)
      ·
        refine ⟨13918005659764638510222775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18557340879686184680297033 13918005659764638510222775)
        ·
          refine ⟨20877008489646957765334163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13918005659764638510222775 20877008489646957765334163)
          ·
            refine ⟨31315512734470436648001245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20877008489646957765334163 31315512734470436648001245)
            ·
              refine ⟨11743317275426413743000467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31315512734470436648001245 11743317275426413743000467)
              ·
                refine ⟨17614975913139620614500701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11743317275426413743000467 17614975913139620614500701)
                ·
                  refine ⟨6605615967427357730437763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17614975913139620614500701 6605615967427357730437763)
                  ·
                    refine ⟨9908423951141036595656645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6605615967427357730437763 9908423951141036595656645)
                    ·
                      refine ⟨1857829490838944361685621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9908423951141036595656645 1857829490838944361685621)
                      ·
                        rfl

theorem cell23_3618110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3618110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618110 prefixEnd_3618110 := by exact prefixLift 3618110
  have htrace : WordTrace (prefixWord ++ tailWord_3618110) baseStart_3618110 baseEnd_3618110 := by
    simpa [prefixWord, tailWord_3618110, baseEnd_3618110] using wordTrace_append hprefix tailTrace_3618110
  have hstable : (prefixWord ++ tailWord_3618110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618110).length < 2 ^ (prefixWord ++ tailWord_3618110).sum := by decide
  have hdescent : baseEnd_3618110 < baseStart_3618110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618143 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_3618143 : Nat := 118140960795 + 3618143 * 2 ^ 59
def prefixEnd_3618143 : Nat := 4983230072969 + 3 ^ 40 * 3618143 * 2
def baseEnd_3618143 : Nat := 1857846435700542732572969

theorem tailTrace_3618143 : CollatzResearch.WordTrace tailWord_3618143 prefixEnd_3618143 1857846435700542732572969 := by
  unfold tailWord_3618143
  simp only [CollatzResearch.WordTrace]
  refine ⟨131964516531093315473619083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87976344354062210315746055 131964516531093315473619083)
  ·
    refine ⟨197946774796639973210428625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131964516531093315473619083 197946774796639973210428625)
    ·
      refine ⟨148460081097479979907821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197946774796639973210428625 148460081097479979907821469)
      ·
        refine ⟨55672530411554992465433051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148460081097479979907821469 55672530411554992465433051)
        ·
          refine ⟨83508795617332488698149577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55672530411554992465433051 83508795617332488698149577)
          ·
            refine ⟨62631596712999366523612183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83508795617332488698149577 62631596712999366523612183)
            ·
              refine ⟨93947395069499049785418275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62631596712999366523612183 93947395069499049785418275)
              ·
                refine ⟨140921092604248574678127413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93947395069499049785418275 140921092604248574678127413)
                ·
                  refine ⟨13211352431648303876074445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140921092604248574678127413 13211352431648303876074445)
                  ·
                    refine ⟨4954257161868113953527917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13211352431648303876074445 4954257161868113953527917)
                    ·
                      refine ⟨1857846435700542732572969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954257161868113953527917 1857846435700542732572969)
                      ·
                        rfl

theorem cell23_3618143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_3618143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618143 prefixEnd_3618143 := by exact prefixLift 3618143
  have htrace : WordTrace (prefixWord ++ tailWord_3618143) baseStart_3618143 baseEnd_3618143 := by
    simpa [prefixWord, tailWord_3618143, baseEnd_3618143] using wordTrace_append hprefix tailTrace_3618143
  have hstable : (prefixWord ++ tailWord_3618143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618143).length < 2 ^ (prefixWord ++ tailWord_3618143).sum := by decide
  have hdescent : baseEnd_3618143 < baseStart_3618143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618160 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_3618160 : Nat := 118140960795 + 3618160 * 2 ^ 59
def prefixEnd_3618160 : Nat := 4983230072969 + 3 ^ 40 * 3618160 * 2
def baseEnd_3618160 : Nat := 1857855164871669166060391

theorem tailTrace_3618160 : CollatzResearch.WordTrace tailWord_3618160 prefixEnd_3618160 1857855164871669166060391 := by
  unfold tailWord_3618160
  simp only [CollatzResearch.WordTrace]
  refine ⟨65982568286015863688493967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87976757714687818251325289 65982568286015863688493967)
  ·
    refine ⟨98973852429023795532740951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65982568286015863688493967 98973852429023795532740951)
    ·
      refine ⟨148460778643535693299111427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98973852429023795532740951 148460778643535693299111427)
      ·
        refine ⟨222691167965303539948667141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148460778643535693299111427 222691167965303539948667141)
        ·
          refine ⟨41754593993494413740375089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222691167965303539948667141 41754593993494413740375089)
          ·
            refine ⟨31315945495120810305281317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41754593993494413740375089 31315945495120810305281317)
            ·
              refine ⟨5871739780335151932240247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31315945495120810305281317 5871739780335151932240247)
              ·
                refine ⟨8807609670502727898360371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871739780335151932240247 8807609670502727898360371)
                ·
                  refine ⟨13211414505754091847540557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807609670502727898360371 13211414505754091847540557)
                  ·
                    refine ⟨4954280439657784442827709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13211414505754091847540557 4954280439657784442827709)
                    ·
                      refine ⟨1857855164871669166060391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954280439657784442827709 1857855164871669166060391)
                      ·
                        rfl

theorem cell23_3618160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_3618160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618160 prefixEnd_3618160 := by exact prefixLift 3618160
  have htrace : WordTrace (prefixWord ++ tailWord_3618160) baseStart_3618160 baseEnd_3618160 := by
    simpa [prefixWord, tailWord_3618160, baseEnd_3618160] using wordTrace_append hprefix tailTrace_3618160
  have hstable : (prefixWord ++ tailWord_3618160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618160).length < 2 ^ (prefixWord ++ tailWord_3618160).sum := by decide
  have hdescent : baseEnd_3618160 < baseStart_3618160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618173 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3618173 : Nat := 118140960795 + 3618173 * 2 ^ 59
def prefixEnd_3618173 : Nat := 4983230072969 + 3 ^ 40 * 3618173 * 2
def baseEnd_3618173 : Nat := 1857861840120177615197831

theorem tailTrace_3618173 : CollatzResearch.WordTrace tailWord_3618173 prefixEnd_3618173 1857861840120177615197831 := by
  unfold tailWord_3618173
  simp only [CollatzResearch.WordTrace]
  refine ⟨131965610720984630597211173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87977073813989753731474115 131965610720984630597211173)
  ·
    refine ⟨24743552010184618236977095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131965610720984630597211173 24743552010184618236977095)
    ·
      refine ⟨37115328015276927355465643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24743552010184618236977095 37115328015276927355465643)
      ·
        refine ⟨55672992022915391033198465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37115328015276927355465643 55672992022915391033198465)
        ·
          refine ⟨41754744017186543274898849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55672992022915391033198465 41754744017186543274898849)
          ·
            refine ⟨31316058012889907456174137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41754744017186543274898849 31316058012889907456174137)
            ·
              refine ⟨23487043509667430592130603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31316058012889907456174137 23487043509667430592130603)
              ·
                refine ⟨35230565264501145888195905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23487043509667430592130603 35230565264501145888195905)
                ·
                  refine ⟨26422923948375859416146929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35230565264501145888195905 26422923948375859416146929)
                  ·
                    refine ⟨19817192961281894562110197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26422923948375859416146929 19817192961281894562110197)
                    ·
                      refine ⟨1857861840120177615197831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19817192961281894562110197 1857861840120177615197831)
                      ·
                        rfl

theorem cell23_3618173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3618173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618173 prefixEnd_3618173 := by exact prefixLift 3618173
  have htrace : WordTrace (prefixWord ++ tailWord_3618173) baseStart_3618173 baseEnd_3618173 := by
    simpa [prefixWord, tailWord_3618173, baseEnd_3618173] using wordTrace_append hprefix tailTrace_3618173
  have hstable : (prefixWord ++ tailWord_3618173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618173).length < 2 ^ (prefixWord ++ tailWord_3618173).sum := by decide
  have hdescent : baseEnd_3618173 < baseStart_3618173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618178 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3618178 : Nat := 118140960795 + 3618178 * 2 ^ 59
def prefixEnd_3618178 : Nat := 4983230072969 + 3 ^ 40 * 3618178 * 2
def baseEnd_3618178 : Nat := 1857864407523450095635309

theorem tailTrace_3618178 : CollatzResearch.WordTrace tailWord_3618178 prefixEnd_3618178 1857864407523450095635309 := by
  unfold tailWord_3618178
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991448271491629112785797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87977195390644344300762125 32991448271491629112785797)
  ·
    refine ⟨6185896550904680458647337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32991448271491629112785797 6185896550904680458647337)
    ·
      refine ⟨4639422413178510343985503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6185896550904680458647337 4639422413178510343985503)
      ·
        refine ⟨6959133619767765515978255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639422413178510343985503 6959133619767765515978255)
        ·
          refine ⟨10438700429651648273967383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959133619767765515978255 10438700429651648273967383)
          ·
            refine ⟨15658050644477472410951075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438700429651648273967383 15658050644477472410951075)
            ·
              refine ⟨23487075966716208616426613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15658050644477472410951075 23487075966716208616426613)
              ·
                refine ⟨2201913371879644557789995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23487075966716208616426613 2201913371879644557789995)
                ·
                  refine ⟨3302870057819466836684993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201913371879644557789995 3302870057819466836684993)
                  ·
                    refine ⟨2477152543364600127513745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302870057819466836684993 2477152543364600127513745)
                    ·
                      refine ⟨1857864407523450095635309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477152543364600127513745 1857864407523450095635309)
                      ·
                        rfl

theorem cell23_3618178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3618178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618178 prefixEnd_3618178 := by exact prefixLift 3618178
  have htrace : WordTrace (prefixWord ++ tailWord_3618178) baseStart_3618178 baseEnd_3618178 := by
    simpa [prefixWord, tailWord_3618178, baseEnd_3618178] using wordTrace_append hprefix tailTrace_3618178
  have hstable : (prefixWord ++ tailWord_3618178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618178).length < 2 ^ (prefixWord ++ tailWord_3618178).sum := by decide
  have hdescent : baseEnd_3618178 < baseStart_3618178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618187 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 1, 3, 2]
def baseStart_3618187 : Nat := 118140960795 + 3618187 * 2 ^ 59
def prefixEnd_3618187 : Nat := 4983230072969 + 3 ^ 40 * 3618187 * 2
def baseEnd_3618187 : Nat := 1857869028849340560422767

theorem tailTrace_3618187 : CollatzResearch.WordTrace tailWord_3618187 prefixEnd_3618187 1857869028849340560422767 := by
  unfold tailWord_3618187
  simp only [CollatzResearch.WordTrace]
  refine ⟨131966121342933910988220815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87977414228622607325480543 131966121342933910988220815)
  ·
    refine ⟨197949182014400866482331223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131966121342933910988220815 197949182014400866482331223)
    ·
      refine ⟨296923773021601299723496835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197949182014400866482331223 296923773021601299723496835)
      ·
        refine ⟨445385659532401949585245253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296923773021601299723496835 445385659532401949585245253)
        ·
          refine ⟨83509811162325365547233485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445385659532401949585245253 83509811162325365547233485)
          ·
            refine ⟨31316179185872012080212557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83509811162325365547233485 31316179185872012080212557)
            ·
              refine ⟨11743567194702004530079709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31316179185872012080212557 11743567194702004530079709)
              ·
                refine ⟨4403837698013251698779891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11743567194702004530079709 4403837698013251698779891)
                ·
                  refine ⟨6605756547019877548169837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403837698013251698779891 6605756547019877548169837)
                  ·
                    refine ⟨2477158705132454080563689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6605756547019877548169837 2477158705132454080563689)
                    ·
                      refine ⟨1857869028849340560422767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477158705132454080563689 1857869028849340560422767)
                      ·
                        rfl

theorem cell23_3618187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3, 2].length) (baseStart_3618187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618187 prefixEnd_3618187 := by exact prefixLift 3618187
  have htrace : WordTrace (prefixWord ++ tailWord_3618187) baseStart_3618187 baseEnd_3618187 := by
    simpa [prefixWord, tailWord_3618187, baseEnd_3618187] using wordTrace_append hprefix tailTrace_3618187
  have hstable : (prefixWord ++ tailWord_3618187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618187).length < 2 ^ (prefixWord ++ tailWord_3618187).sum := by decide
  have hdescent : baseEnd_3618187 < baseStart_3618187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618210 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3618210 : Nat := 118140960795 + 3618210 * 2 ^ 59
def prefixEnd_3618210 : Nat := 4983230072969 + 3 ^ 40 * 3618210 * 2
def baseEnd_3618210 : Nat := 619293612968131323478387

theorem tailTrace_3618210 : CollatzResearch.WordTrace tailWord_3618210 prefixEnd_3618210 619293612968131323478387 := by
  unfold tailWord_3618210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991740055462646479077021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87977973481233723944205389 32991740055462646479077021)
  ·
    refine ⟨12371902520798492429653883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32991740055462646479077021 12371902520798492429653883)
    ·
      refine ⟨18557853781197738644480825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371902520798492429653883 18557853781197738644480825)
      ·
        refine ⟨13918390335898303983360619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18557853781197738644480825 13918390335898303983360619)
        ·
          refine ⟨20877585503847455975040929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13918390335898303983360619 20877585503847455975040929)
          ·
            refine ⟨15658189127885591981280697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20877585503847455975040929 15658189127885591981280697)
            ·
              refine ⟨11743641845914193985960523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15658189127885591981280697 11743641845914193985960523)
              ·
                refine ⟨17615462768871290978940785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11743641845914193985960523 17615462768871290978940785)
                ·
                  refine ⟨13211597076653468234205589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17615462768871290978940785 13211597076653468234205589)
                  ·
                    refine ⟨619293612968131323478387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13211597076653468234205589 619293612968131323478387)
                    ·
                      rfl

theorem cell23_3618210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3618210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618210 prefixEnd_3618210 := by exact prefixLift 3618210
  have htrace : WordTrace (prefixWord ++ tailWord_3618210) baseStart_3618210 baseEnd_3618210 := by
    simpa [prefixWord, tailWord_3618210, baseEnd_3618210] using wordTrace_append hprefix tailTrace_3618210
  have hstable : (prefixWord ++ tailWord_3618210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618210).length < 2 ^ (prefixWord ++ tailWord_3618210).sum := by decide
  have hdescent : baseEnd_3618210 < baseStart_3618210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618213 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3618213 : Nat := 118140960795 + 3618213 * 2 ^ 59
def prefixEnd_3618213 : Nat := 4983230072969 + 3 ^ 40 * 3618213 * 2
def baseEnd_3618213 : Nat := 1857882379346357458697647

theorem tailTrace_3618213 : CollatzResearch.WordTrace tailWord_3618213 prefixEnd_3618213 1857882379346357458697647 := by
  unfold tailWord_3618213
  simp only [CollatzResearch.WordTrace]
  refine ⟨131967069640839717428667293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87978046427226478285778195 131967069640839717428667293)
  ·
    refine ⟨49487651115314894035750235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131967069640839717428667293 49487651115314894035750235)
    ·
      refine ⟨74231476672972341053625353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49487651115314894035750235 74231476672972341053625353)
      ·
        refine ⟨55673607504729255790219015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74231476672972341053625353 55673607504729255790219015)
        ·
          refine ⟨83510411257093883685328523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55673607504729255790219015 83510411257093883685328523)
          ·
            refine ⟨125265616885640825527992785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83510411257093883685328523 125265616885640825527992785)
            ·
              refine ⟨93949212664230619145994589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125265616885640825527992785 93949212664230619145994589)
              ·
                refine ⟨35230954749086482179747971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93949212664230619145994589 35230954749086482179747971)
                ·
                  refine ⟨52846432123629723269621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35230954749086482179747971 52846432123629723269621957)
                  ·
                    refine ⟨9908706023180573113054117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52846432123629723269621957 9908706023180573113054117)
                    ·
                      refine ⟨1857882379346357458697647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9908706023180573113054117 1857882379346357458697647)
                      ·
                        rfl

theorem cell23_3618213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3618213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618213 prefixEnd_3618213 := by exact prefixLift 3618213
  have htrace : WordTrace (prefixWord ++ tailWord_3618213) baseStart_3618213 baseEnd_3618213 := by
    simpa [prefixWord, tailWord_3618213, baseEnd_3618213] using wordTrace_append hprefix tailTrace_3618213
  have hstable : (prefixWord ++ tailWord_3618213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618213).length < 2 ^ (prefixWord ++ tailWord_3618213).sum := by decide
  have hdescent : baseEnd_3618213 < baseStart_3618213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618221 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3618221 : Nat := 118140960795 + 3618221 * 2 ^ 59
def prefixEnd_3618221 : Nat := 4983230072969 + 3 ^ 40 * 3618221 * 2
def baseEnd_3618221 : Nat := 1857886487191593427397611

theorem tailTrace_3618221 : CollatzResearch.WordTrace tailWord_3618221 prefixEnd_3618221 1857886487191593427397611 := by
  unfold tailWord_3618221
  simp only [CollatzResearch.WordTrace]
  refine ⟨131967361424810734794958517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87978240949873823196639011 131967361424810734794958517)
  ·
    refine ⟨12371940133576006387027361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131967361424810734794958517 12371940133576006387027361)
    ·
      refine ⟨9278955100182004790270521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12371940133576006387027361 9278955100182004790270521)
      ·
        refine ⟨6959216325136503592702891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278955100182004790270521 6959216325136503592702891)
        ·
          refine ⟨10438824487704755389054337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959216325136503592702891 10438824487704755389054337)
          ·
            refine ⟨7829118365778566541790753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10438824487704755389054337 7829118365778566541790753)
            ·
              refine ⟨5871838774333924906343065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829118365778566541790753 5871838774333924906343065)
              ·
                refine ⟨4403879080750443679757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871838774333924906343065 4403879080750443679757299)
                ·
                  refine ⟨6605818621125665519635949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403879080750443679757299 6605818621125665519635949)
                  ·
                    refine ⟨2477181982922124569863481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6605818621125665519635949 2477181982922124569863481)
                    ·
                      refine ⟨1857886487191593427397611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477181982922124569863481 1857886487191593427397611)
                      ·
                        rfl

theorem cell23_3618221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3618221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618221 prefixEnd_3618221 := by exact prefixLift 3618221
  have htrace : WordTrace (prefixWord ++ tailWord_3618221) baseStart_3618221 baseEnd_3618221 := by
    simpa [prefixWord, tailWord_3618221, baseEnd_3618221] using wordTrace_append hprefix tailTrace_3618221
  have hstable : (prefixWord ++ tailWord_3618221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618221).length < 2 ^ (prefixWord ++ tailWord_3618221).sum := by decide
  have hdescent : baseEnd_3618221 < baseStart_3618221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618308 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 5]
def baseStart_3618308 : Nat := 118140960795 + 3618308 * 2 ^ 59
def prefixEnd_3618308 : Nat := 4983230072969 + 3 ^ 40 * 3618308 * 2
def baseEnd_3618308 : Nat := 206436795556503843001079

theorem tailTrace_3618308 : CollatzResearch.WordTrace tailWord_3618308 prefixEnd_3618308 206436795556503843001079 := by
  unfold tailWord_3618308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65985267287747774326687789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87980356383663699102250385 65985267287747774326687789)
  ·
    refine ⟨24744475232905415372507921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65985267287747774326687789 24744475232905415372507921)
    ·
      refine ⟨18558356424679061529380941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24744475232905415372507921 18558356424679061529380941)
      ·
        refine ⟨6959383659254648073517853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18558356424679061529380941 6959383659254648073517853)
        ·
          refine ⟨2609768872220493027569195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959383659254648073517853 2609768872220493027569195)
          ·
            refine ⟨3914653308330739541353793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609768872220493027569195 3914653308330739541353793)
            ·
              refine ⟨2935989981248054656015345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914653308330739541353793 2935989981248054656015345)
              ·
                refine ⟨2201992485936040992011509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935989981248054656015345 2201992485936040992011509)
                ·
                  refine ⟨206436795556503843001079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201992485936040992011509 206436795556503843001079)
                  ·
                    rfl

theorem cell23_3618308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_3618308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618308 prefixEnd_3618308 := by exact prefixLift 3618308
  have htrace : WordTrace (prefixWord ++ tailWord_3618308) baseStart_3618308 baseEnd_3618308 := by
    simpa [prefixWord, tailWord_3618308, baseEnd_3618308] using wordTrace_append hprefix tailTrace_3618308
  have hstable : (prefixWord ++ tailWord_3618308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618308).length < 2 ^ (prefixWord ++ tailWord_3618308).sum := by decide
  have hdescent : baseEnd_3618308 < baseStart_3618308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618344 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3618344 : Nat := 118140960795 + 3618344 * 2 ^ 59
def prefixEnd_3618344 : Nat := 4983230072969 + 3 ^ 40 * 3618344 * 2
def baseEnd_3618344 : Nat := 1857949645312096446159545

theorem tailTrace_3618344 : CollatzResearch.WordTrace tailWord_3618344 prefixEnd_3618344 1857949645312096446159545 := by
  unfold tailWord_3618344
  simp only [CollatzResearch.WordTrace]
  refine ⟨65985923801682563400843043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87981231735576751201124057 65985923801682563400843043)
  ·
    refine ⟨98978885702523845101264565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65985923801682563400843043 98978885702523845101264565)
    ·
      refine ⟨9279270534611610478243553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98978885702523845101264565 9279270534611610478243553)
      ·
        refine ⟨6959452900958707858682665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9279270534611610478243553 6959452900958707858682665)
        ·
          refine ⟨5219589675719030894011999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959452900958707858682665 5219589675719030894011999)
          ·
            refine ⟨7829384513578546341017999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219589675719030894011999 7829384513578546341017999)
            ·
              refine ⟨11744076770367819511526999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829384513578546341017999 11744076770367819511526999)
              ·
                refine ⟨17616115155551729267290499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11744076770367819511526999 17616115155551729267290499)
                ·
                  refine ⟨26424172733327593900935749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17616115155551729267290499 26424172733327593900935749)
                  ·
                    refine ⟨4954532387498923856425453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26424172733327593900935749 4954532387498923856425453)
                    ·
                      refine ⟨1857949645312096446159545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954532387498923856425453 1857949645312096446159545)
                      ·
                        rfl

theorem cell23_3618344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3618344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618344 prefixEnd_3618344 := by exact prefixLift 3618344
  have htrace : WordTrace (prefixWord ++ tailWord_3618344) baseStart_3618344 baseEnd_3618344 := by
    simpa [prefixWord, tailWord_3618344, baseEnd_3618344] using wordTrace_append hprefix tailTrace_3618344
  have hstable : (prefixWord ++ tailWord_3618344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618344).length < 2 ^ (prefixWord ++ tailWord_3618344).sum := by decide
  have hdescent : baseEnd_3618344 < baseStart_3618344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618364 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 6]
def baseStart_3618364 : Nat := 118140960795 + 3618364 * 2 ^ 59
def prefixEnd_3618364 : Nat := 4983230072969 + 3 ^ 40 * 3618364 * 2
def baseEnd_3618364 : Nat := 206439990547242929767717

theorem tailTrace_3618364 : CollatzResearch.WordTrace tailWord_3618364 prefixEnd_3618364 206439990547242929767717 := by
  unfold tailWord_3618364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65986288531646335108707073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87981718042195113478276097 65986288531646335108707073)
  ·
    refine ⟨49489716398734751331530305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65986288531646335108707073 49489716398734751331530305)
    ·
      refine ⟨37117287299051063498647729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49489716398734751331530305 37117287299051063498647729)
      ·
        refine ⟨27837965474288297623985797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37117287299051063498647729 27837965474288297623985797)
        ·
          refine ⟨5219618526429055804497337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27837965474288297623985797 5219618526429055804497337)
          ·
            refine ⟨3914713894821791853373003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219618526429055804497337 3914713894821791853373003)
            ·
              refine ⟨5872070842232687780059505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914713894821791853373003 5872070842232687780059505)
              ·
                refine ⟨4404053131674515835044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872070842232687780059505 4404053131674515835044629)
                ·
                  refine ⟨206439990547242929767717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4404053131674515835044629 206439990547242929767717)
                  ·
                    rfl

theorem cell23_3618364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_3618364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618364 prefixEnd_3618364 := by exact prefixLift 3618364
  have htrace : WordTrace (prefixWord ++ tailWord_3618364) baseStart_3618364 baseEnd_3618364 := by
    simpa [prefixWord, tailWord_3618364, baseEnd_3618364] using wordTrace_append hprefix tailTrace_3618364
  have hstable : (prefixWord ++ tailWord_3618364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618364).length < 2 ^ (prefixWord ++ tailWord_3618364).sum := by decide
  have hdescent : baseEnd_3618364 < baseStart_3618364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618381 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3618381 : Nat := 118140960795 + 3618381 * 2 ^ 59
def prefixEnd_3618381 : Nat := 4983230072969 + 3 ^ 40 * 3618381 * 2
def baseEnd_3618381 : Nat := 206440960455145866821875

theorem tailTrace_3618381 : CollatzResearch.WordTrace tailWord_3618381 prefixEnd_3618381 206440960455145866821875 := by
  unfold tailWord_3618381
  simp only [CollatzResearch.WordTrace]
  refine ⟨131973197104231082120782997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87982131402820721413855331 131973197104231082120782997)
  ·
    refine ⟨6186243614260831974411703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131973197104231082120782997 6186243614260831974411703)
    ·
      refine ⟨9279365421391247961617555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186243614260831974411703 9279365421391247961617555)
      ·
        refine ⟨13919048132086871942426333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279365421391247961617555 13919048132086871942426333)
        ·
          refine ⟨5219643049532576978409875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13919048132086871942426333 5219643049532576978409875)
          ·
            refine ⟨7829464574298865467614813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219643049532576978409875 7829464574298865467614813)
            ·
              refine ⟨2936049215362074550355555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7829464574298865467614813 2936049215362074550355555)
              ·
                refine ⟨4404073823043111825533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936049215362074550355555 4404073823043111825533333)
                ·
                  refine ⟨206440960455145866821875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4404073823043111825533333 206440960455145866821875)
                  ·
                    rfl

theorem cell23_3618381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3618381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618381 prefixEnd_3618381 := by exact prefixLift 3618381
  have htrace : WordTrace (prefixWord ++ tailWord_3618381) baseStart_3618381 baseEnd_3618381 := by
    simpa [prefixWord, tailWord_3618381, baseEnd_3618381] using wordTrace_append hprefix tailTrace_3618381
  have hstable : (prefixWord ++ tailWord_3618381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618381).length < 2 ^ (prefixWord ++ tailWord_3618381).sum := by decide
  have hdescent : baseEnd_3618381 < baseStart_3618381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618400 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3618400 : Nat := 118140960795 + 3618400 * 2 ^ 59
def prefixEnd_3618400 : Nat := 4983230072969 + 3 ^ 40 * 3618400 * 2
def baseEnd_3618400 : Nat := 1857978400228748227059287

theorem tailTrace_3618400 : CollatzResearch.WordTrace tailWord_3618400 prefixEnd_3618400 1857978400228748227059287 := by
  unfold tailWord_3618400
  simp only [CollatzResearch.WordTrace]
  refine ⟨65986945045581124182862327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87982593394108165577149769 65986945045581124182862327)
  ·
    refine ⟨98980417568371686274293491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65986945045581124182862327 98980417568371686274293491)
    ·
      refine ⟨148470626352557529411440237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98980417568371686274293491 148470626352557529411440237)
      ·
        refine ⟨55676484882209073529290089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148470626352557529411440237 55676484882209073529290089)
        ·
          refine ⟨41757363661656805146967567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55676484882209073529290089 41757363661656805146967567)
          ·
            refine ⟨62636045492485207720451351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41757363661656805146967567 62636045492485207720451351)
            ·
              refine ⟨93954068238727811580677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62636045492485207720451351 93954068238727811580677027)
              ·
                refine ⟨140931102358091717371015541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93954068238727811580677027 140931102358091717371015541)
                ·
                  refine ⟨13212290846071098503532707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140931102358091717371015541 13212290846071098503532707)
                  ·
                    refine ⟨19818436269106647755299061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13212290846071098503532707 19818436269106647755299061)
                    ·
                      refine ⟨1857978400228748227059287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19818436269106647755299061 1857978400228748227059287)
                      ·
                        rfl

theorem cell23_3618400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3618400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618400 prefixEnd_3618400 := by exact prefixLift 3618400
  have htrace : WordTrace (prefixWord ++ tailWord_3618400) baseStart_3618400 baseEnd_3618400 := by
    simpa [prefixWord, tailWord_3618400, baseEnd_3618400] using wordTrace_append hprefix tailTrace_3618400
  have hstable : (prefixWord ++ tailWord_3618400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618400).length < 2 ^ (prefixWord ++ tailWord_3618400).sum := by decide
  have hdescent : baseEnd_3618400 < baseStart_3618400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618407 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3618407 : Nat := 118140960795 + 3618407 * 2 ^ 59
def prefixEnd_3618407 : Nat := 4983230072969 + 3 ^ 40 * 3618407 * 2
def baseEnd_3618407 : Nat := 619327331531109899890585

theorem tailTrace_3618407 : CollatzResearch.WordTrace tailWord_3618407 prefixEnd_3618407 619327331531109899890585 := by
  unfold tailWord_3618407
  simp only [CollatzResearch.WordTrace]
  refine ⟨131974145402136888561229475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87982763601424592374152983 131974145402136888561229475)
  ·
    refine ⟨197961218103205332841844213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131974145402136888561229475 197961218103205332841844213)
    ·
      refine ⟨18558864197175499953922895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197961218103205332841844213 18558864197175499953922895)
      ·
        refine ⟨27838296295763249930884343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18558864197175499953922895 27838296295763249930884343)
        ·
          refine ⟨41757444443644874896326515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27838296295763249930884343 41757444443644874896326515)
          ·
            refine ⟨62636166665467312344489773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41757444443644874896326515 62636166665467312344489773)
            ·
              refine ⟨23488562499550242129183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62636166665467312344489773 23488562499550242129183665)
              ·
                refine ⟨17616421874662681596887749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23488562499550242129183665 17616421874662681596887749)
                ·
                  refine ⟨3303079101499252799416453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17616421874662681596887749 3303079101499252799416453)
                  ·
                    refine ⟨619327331531109899890585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303079101499252799416453 619327331531109899890585)
                    ·
                      rfl

theorem cell23_3618407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3618407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618407 prefixEnd_3618407 := by exact prefixLift 3618407
  have htrace : WordTrace (prefixWord ++ tailWord_3618407) baseStart_3618407 baseEnd_3618407 := by
    simpa [prefixWord, tailWord_3618407, baseEnd_3618407] using wordTrace_append hprefix tailTrace_3618407
  have hstable : (prefixWord ++ tailWord_3618407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618407).length < 2 ^ (prefixWord ++ tailWord_3618407).sum := by decide
  have hdescent : baseEnd_3618407 < baseStart_3618407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618408 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3618408 : Nat := 118140960795 + 3618408 * 2 ^ 59
def prefixEnd_3618408 : Nat := 4983230072969 + 3 ^ 40 * 3618408 * 2
def baseEnd_3618408 : Nat := 1857982508073984195759251

theorem tailTrace_3618408 : CollatzResearch.WordTrace tailWord_3618408 prefixEnd_3618408 1857982508073984195759251 := by
  unfold tailWord_3618408
  simp only [CollatzResearch.WordTrace]
  refine ⟨65987090937566632866007939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87982787916755510488010585 65987090937566632866007939)
  ·
    refine ⟨98980636406349949299011909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65987090937566632866007939 98980636406349949299011909)
    ·
      refine ⟨18558869326190615493564733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98980636406349949299011909 18558869326190615493564733)
      ·
        refine ⟨6959575997321480810086775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18558869326190615493564733 6959575997321480810086775)
        ·
          refine ⟨10439363995982221215130163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959575997321480810086775 10439363995982221215130163)
          ·
            refine ⟨15659045993973331822695245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439363995982221215130163 15659045993973331822695245)
            ·
              refine ⟨5872142247739999433510717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15659045993973331822695245 5872142247739999433510717)
              ·
                refine ⟨2202053342902499787566519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872142247739999433510717 2202053342902499787566519)
                ·
                  refine ⟨3303080014353749681349779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202053342902499787566519 3303080014353749681349779)
                  ·
                    refine ⟨4954620021530624522024669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303080014353749681349779 4954620021530624522024669)
                    ·
                      refine ⟨1857982508073984195759251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954620021530624522024669 1857982508073984195759251)
                      ·
                        rfl

theorem cell23_3618408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3618408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618408 prefixEnd_3618408 := by exact prefixLift 3618408
  have htrace : WordTrace (prefixWord ++ tailWord_3618408) baseStart_3618408 baseEnd_3618408 := by
    simpa [prefixWord, tailWord_3618408, baseEnd_3618408] using wordTrace_append hprefix tailTrace_3618408
  have hstable : (prefixWord ++ tailWord_3618408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618408).length < 2 ^ (prefixWord ++ tailWord_3618408).sum := by decide
  have hdescent : baseEnd_3618408 < baseStart_3618408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618464 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3618464 : Nat := 118140960795 + 3618464 * 2 ^ 59
def prefixEnd_3618464 : Nat := 4983230072969 + 3 ^ 40 * 3618464 * 2
def baseEnd_3618464 : Nat := 1858011262990635976658993

theorem tailTrace_3618464 : CollatzResearch.WordTrace tailWord_3618464 prefixEnd_3618464 1858011262990635976658993 := by
  unfold tailWord_3618464
  simp only [CollatzResearch.WordTrace]
  refine ⟨65988112181465193648027223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87984149575286924864036297 65988112181465193648027223)
  ·
    refine ⟨98982168272197790472040835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65988112181465193648027223 98982168272197790472040835)
    ·
      refine ⟨148473252408296685708061253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98982168272197790472040835 148473252408296685708061253)
      ·
        refine ⟨27838734826555628570261485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148473252408296685708061253 27838734826555628570261485)
        ·
          refine ⟨10439525559958360713848057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27838734826555628570261485 10439525559958360713848057)
          ·
            refine ⟨7829644169968770535386043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439525559958360713848057 7829644169968770535386043)
            ·
              refine ⟨11744466254953155803079065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829644169968770535386043 11744466254953155803079065)
              ·
                refine ⟨8808349691214866852309299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744466254953155803079065 8808349691214866852309299)
                ·
                  refine ⟨13212524536822300278463949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8808349691214866852309299 13212524536822300278463949)
                  ·
                    refine ⟨4954696701308362604423981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13212524536822300278463949 4954696701308362604423981)
                    ·
                      refine ⟨1858011262990635976658993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954696701308362604423981 1858011262990635976658993)
                      ·
                        rfl

theorem cell23_3618464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3618464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618464 prefixEnd_3618464 := by exact prefixLift 3618464
  have htrace : WordTrace (prefixWord ++ tailWord_3618464) baseStart_3618464 baseEnd_3618464 := by
    simpa [prefixWord, tailWord_3618464, baseEnd_3618464] using wordTrace_append hprefix tailTrace_3618464
  have hstable : (prefixWord ++ tailWord_3618464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618464).length < 2 ^ (prefixWord ++ tailWord_3618464).sum := by decide
  have hdescent : baseEnd_3618464 < baseStart_3618464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618487 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_3618487 : Nat := 118140960795 + 3618487 * 2 ^ 59
def prefixEnd_3618487 : Nat := 4983230072969 + 3 ^ 40 * 3618487 * 2
def baseEnd_3618487 : Nat := 1858023073045689386671387

theorem tailTrace_3618487 : CollatzResearch.WordTrace tailWord_3618487 prefixEnd_3618487 1858023073045689386671387 := by
  unfold tailWord_3618487
  simp only [CollatzResearch.WordTrace]
  refine ⟨131977063241847062224141715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87984708827898041482761143 131977063241847062224141715)
  ·
    refine ⟨197965594862770593336212573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131977063241847062224141715 197965594862770593336212573)
    ·
      refine ⟨74237098073538972501079715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197965594862770593336212573 74237098073538972501079715)
      ·
        refine ⟨111355647110308458751619573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74237098073538972501079715 111355647110308458751619573)
        ·
          refine ⟨10439591916591418007964335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111355647110308458751619573 10439591916591418007964335)
          ·
            refine ⟨15659387874887127011946503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439591916591418007964335 15659387874887127011946503)
            ·
              refine ⟨23489081812330690517919755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15659387874887127011946503 23489081812330690517919755)
              ·
                refine ⟨35233622718496035776879633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23489081812330690517919755 35233622718496035776879633)
                ·
                  refine ⟨26425217038872026832659725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35233622718496035776879633 26425217038872026832659725)
                  ·
                    refine ⟨9909456389577010062247397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26425217038872026832659725 9909456389577010062247397)
                    ·
                      refine ⟨1858023073045689386671387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9909456389577010062247397 1858023073045689386671387)
                      ·
                        rfl

theorem cell23_3618487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_3618487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618487 prefixEnd_3618487 := by exact prefixLift 3618487
  have htrace : WordTrace (prefixWord ++ tailWord_3618487) baseStart_3618487 baseEnd_3618487 := by
    simpa [prefixWord, tailWord_3618487, baseEnd_3618487] using wordTrace_append hprefix tailTrace_3618487
  have hstable : (prefixWord ++ tailWord_3618487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618487).length < 2 ^ (prefixWord ++ tailWord_3618487).sum := by decide
  have hdescent : baseEnd_3618487 < baseStart_3618487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618525 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3618525 : Nat := 118140960795 + 3618525 * 2 ^ 59
def prefixEnd_3618525 : Nat := 4983230072969 + 3 ^ 40 * 3618525 * 2
def baseEnd_3618525 : Nat := 1858042585310560237996213

theorem tailTrace_3618525 : CollatzResearch.WordTrace tailWord_3618525 prefixEnd_3618525 1858042585310560237996213 := by
  unfold tailWord_3618525
  simp only [CollatzResearch.WordTrace]
  refine ⟨131978449215709394714025029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87985632810472929809350019 131978449215709394714025029)
  ·
    refine ⟨24745959227945511508879693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131978449215709394714025029 24745959227945511508879693)
    ·
      refine ⟨9279734710479566815829885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24745959227945511508879693 9279734710479566815829885)
      ·
        refine ⟨3479900516429837555936207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9279734710479566815829885 3479900516429837555936207)
        ·
          refine ⟨5219850774644756333904311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479900516429837555936207 5219850774644756333904311)
          ·
            refine ⟨7829776161967134500856467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219850774644756333904311 7829776161967134500856467)
            ·
              refine ⟨11744664242950701751284701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829776161967134500856467 11744664242950701751284701)
              ·
                refine ⟨4404249091106513156731763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11744664242950701751284701 4404249091106513156731763)
                ·
                  refine ⟨6606373636659769735097645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404249091106513156731763 6606373636659769735097645)
                  ·
                    refine ⟨2477390113747413650661617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6606373636659769735097645 2477390113747413650661617)
                    ·
                      refine ⟨1858042585310560237996213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477390113747413650661617 1858042585310560237996213)
                      ·
                        rfl

theorem cell23_3618525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3618525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618525 prefixEnd_3618525 := by exact prefixLift 3618525
  have htrace : WordTrace (prefixWord ++ tailWord_3618525) baseStart_3618525 baseEnd_3618525 := by
    simpa [prefixWord, tailWord_3618525, baseEnd_3618525] using wordTrace_append hprefix tailTrace_3618525
  have hstable : (prefixWord ++ tailWord_3618525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618525).length < 2 ^ (prefixWord ++ tailWord_3618525).sum := by decide
  have hdescent : baseEnd_3618525 < baseStart_3618525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618538 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_3618538 : Nat := 118140960795 + 3618538 * 2 ^ 59
def prefixEnd_3618538 : Nat := 4983230072969 + 3 ^ 40 * 3618538 * 2
def baseEnd_3618538 : Nat := 1858049260559068687133653

theorem tailTrace_3618538 : CollatzResearch.WordTrace tailWord_3618538 prefixEnd_3618538 1858049260559068687133653 := by
  unfold tailWord_3618538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32994730841165574483562067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87985948909774865289498845 32994730841165574483562067)
  ·
    refine ⟨49492096261748361725343101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32994730841165574483562067 49492096261748361725343101)
    ·
      refine ⟨18559536098155635647003663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49492096261748361725343101 18559536098155635647003663)
      ·
        refine ⟨27839304147233453470505495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18559536098155635647003663 27839304147233453470505495)
        ·
          refine ⟨41758956220850180205758243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27839304147233453470505495 41758956220850180205758243)
          ·
            refine ⟨62638434331275270308637365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41758956220850180205758243 62638434331275270308637365)
            ·
              refine ⟨5872353218557056591434753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62638434331275270308637365 5872353218557056591434753)
              ·
                refine ⟨4404264913917792443576065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872353218557056591434753 4404264913917792443576065)
                ·
                  refine ⟨3303198685438344332682049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404264913917792443576065 3303198685438344332682049)
                  ·
                    refine ⟨2477399014078758249511537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3303198685438344332682049 2477399014078758249511537)
                    ·
                      refine ⟨1858049260559068687133653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477399014078758249511537 1858049260559068687133653)
                      ·
                        rfl

theorem cell23_3618538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_3618538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618538 prefixEnd_3618538 := by exact prefixLift 3618538
  have htrace : WordTrace (prefixWord ++ tailWord_3618538) baseStart_3618538 baseEnd_3618538 := by
    simpa [prefixWord, tailWord_3618538, baseEnd_3618538] using wordTrace_append hprefix tailTrace_3618538
  have hstable : (prefixWord ++ tailWord_3618538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618538).length < 2 ^ (prefixWord ++ tailWord_3618538).sum := by decide
  have hdescent : baseEnd_3618538 < baseStart_3618538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618557 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_3618557 : Nat := 118140960795 + 3618557 * 2 ^ 59
def prefixEnd_3618557 : Nat := 4983230072969 + 3 ^ 40 * 3618557 * 2
def baseEnd_3618557 : Nat := 619353005563834704265355

theorem tailTrace_3618557 : CollatzResearch.WordTrace tailWord_3618557 prefixEnd_3618557 619353005563834704265355 := by
  unfold tailWord_3618557
  simp only [CollatzResearch.WordTrace]
  refine ⟨131979616351593464179189925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87986410901062309452793283 131979616351593464179189925)
  ·
    refine ⟨24746178065923774533598111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131979616351593464179189925 24746178065923774533598111)
    ·
      refine ⟨37119267098885661800397167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24746178065923774533598111 37119267098885661800397167)
      ·
        refine ⟨55678900648328492700595751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37119267098885661800397167 55678900648328492700595751)
        ·
          refine ⟨83518350972492739050893627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55678900648328492700595751 83518350972492739050893627)
          ·
            refine ⟨125277526458739108576340441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83518350972492739050893627 125277526458739108576340441)
            ·
              refine ⟨93958144844054331432255331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125277526458739108576340441 93958144844054331432255331)
              ·
                refine ⟨140937217266081497148382997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93958144844054331432255331 140937217266081497148382997)
                ·
                  refine ⟨6606432059347570178830453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140937217266081497148382997 6606432059347570178830453)
                  ·
                    refine ⟨619353005563834704265355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6606432059347570178830453 619353005563834704265355)
                    ·
                      rfl

theorem cell23_3618557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_3618557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618557 prefixEnd_3618557 := by exact prefixLift 3618557
  have htrace : WordTrace (prefixWord ++ tailWord_3618557) baseStart_3618557 baseEnd_3618557 := by
    simpa [prefixWord, tailWord_3618557, baseEnd_3618557] using wordTrace_append hprefix tailTrace_3618557
  have hstable : (prefixWord ++ tailWord_3618557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618557).length < 2 ^ (prefixWord ++ tailWord_3618557).sum := by decide
  have hdescent : baseEnd_3618557 < baseStart_3618557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618578 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_3618578 : Nat := 118140960795 + 3618578 * 2 ^ 59
def prefixEnd_3618578 : Nat := 4983230072969 + 3 ^ 40 * 3618578 * 2
def baseEnd_3618578 : Nat := 206452199976138725625941

theorem tailTrace_3618578 : CollatzResearch.WordTrace tailWord_3618578 prefixEnd_3618578 206452199976138725625941 := by
  unfold tailWord_3618578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32995095571129346191426097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87986921523011589843802925 32995095571129346191426097)
  ·
    refine ⟨24746321678347009643569573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32995095571129346191426097 24746321678347009643569573)
    ·
      refine ⟨4639935314690064308169295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24746321678347009643569573 4639935314690064308169295)
      ·
        refine ⟨6959902972035096462253943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639935314690064308169295 6959902972035096462253943)
        ·
          refine ⟨10439854458052644693380915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959902972035096462253943 10439854458052644693380915)
          ·
            refine ⟨15659781687078967040071373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439854458052644693380915 15659781687078967040071373)
            ·
              refine ⟨5872418132654612640026765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15659781687078967040071373 5872418132654612640026765)
              ·
                refine ⟨2202156799745479740010037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872418132654612640026765 2202156799745479740010037)
                ·
                  refine ⟨206452199976138725625941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202156799745479740010037 206452199976138725625941)
                  ·
                    rfl

theorem cell23_3618578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_3618578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618578 prefixEnd_3618578 := by exact prefixLift 3618578
  have htrace : WordTrace (prefixWord ++ tailWord_3618578) baseStart_3618578 baseEnd_3618578 := by
    simpa [prefixWord, tailWord_3618578, baseEnd_3618578] using wordTrace_append hprefix tailTrace_3618578
  have hstable : (prefixWord ++ tailWord_3618578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618578).length < 2 ^ (prefixWord ++ tailWord_3618578).sum := by decide
  have hdescent : baseEnd_3618578 < baseStart_3618578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618655 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 1, 4]
def baseStart_3618655 : Nat := 118140960795 + 3618655 * 2 ^ 59
def prefixEnd_3618655 : Nat := 4983230072969 + 3 ^ 40 * 3618655 * 2
def baseEnd_3618655 : Nat := 619369779265214909790205

theorem tailTrace_3618655 : CollatzResearch.WordTrace tailWord_3618655 prefixEnd_3618655 619369779265214909790205 := by
  unfold tailWord_3618655
  simp only [CollatzResearch.WordTrace]
  refine ⟨131983190705238426916257419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87988793803492284610838279 131983190705238426916257419)
  ·
    refine ⟨197974786057857640374386129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131983190705238426916257419 197974786057857640374386129)
    ·
      refine ⟨148481089543393230280789597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197974786057857640374386129 148481089543393230280789597)
      ·
        refine ⟨55680408578772461355296099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148481089543393230280789597 55680408578772461355296099)
        ·
          refine ⟨83520612868158692032944149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55680408578772461355296099 83520612868158692032944149)
          ·
            refine ⟨3915028728194938689044257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83520612868158692032944149 3915028728194938689044257)
            ·
              refine ⟨2936271546146204016783193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915028728194938689044257 2936271546146204016783193)
              ·
                refine ⟨2202203659609653012587395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936271546146204016783193 2202203659609653012587395)
                ·
                  refine ⟨3303305489414479518881093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202203659609653012587395 3303305489414479518881093)
                  ·
                    refine ⟨619369779265214909790205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303305489414479518881093 619369779265214909790205)
                    ·
                      rfl

theorem cell23_3618655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_3618655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618655 prefixEnd_3618655 := by exact prefixLift 3618655
  have htrace : WordTrace (prefixWord ++ tailWord_3618655) baseStart_3618655 baseEnd_3618655 := by
    simpa [prefixWord, tailWord_3618655, baseEnd_3618655] using wordTrace_append hprefix tailTrace_3618655
  have hstable : (prefixWord ++ tailWord_3618655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618655).length < 2 ^ (prefixWord ++ tailWord_3618655).sum := by decide
  have hdescent : baseEnd_3618655 < baseStart_3618655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618661 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3618661 : Nat := 118140960795 + 3618661 * 2 ^ 59
def prefixEnd_3618661 : Nat := 4983230072969 + 3 ^ 40 * 3618661 * 2
def baseEnd_3618661 : Nat := 1858112418679571705895587

theorem tailTrace_3618661 : CollatzResearch.WordTrace tailWord_3618661 prefixEnd_3618661 1858112418679571705895587 := by
  unfold tailWord_3618661
  simp only [CollatzResearch.WordTrace]
  refine ⟨131983409543216689940975837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87988939695477793293983891 131983409543216689940975837)
  ·
    refine ⟨49493778578706258727865939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131983409543216689940975837 49493778578706258727865939)
    ·
      refine ⟨74240667868059388091798909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49493778578706258727865939 74240667868059388091798909)
      ·
        refine ⟨27840250450522270534424591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74240667868059388091798909 27840250450522270534424591)
        ·
          refine ⟨41760375675783405801636887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27840250450522270534424591 41760375675783405801636887)
          ·
            refine ⟨62640563513675108702455331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41760375675783405801636887 62640563513675108702455331)
            ·
              refine ⟨93960845270512663053682997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62640563513675108702455331 93960845270512663053682997)
              ·
                refine ⟨8808829244110562161282781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93960845270512663053682997 8808829244110562161282781)
                ·
                  refine ⟨3303310966541460810481043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8808829244110562161282781 3303310966541460810481043)
                  ·
                    refine ⟨4954966449812191215721565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303310966541460810481043 4954966449812191215721565)
                    ·
                      refine ⟨1858112418679571705895587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4954966449812191215721565 1858112418679571705895587)
                      ·
                        rfl

theorem cell23_3618661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3618661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618661 prefixEnd_3618661 := by exact prefixLift 3618661
  have htrace : WordTrace (prefixWord ++ tailWord_3618661) baseStart_3618661 baseEnd_3618661 := by
    simpa [prefixWord, tailWord_3618661, baseEnd_3618661] using wordTrace_append hprefix tailTrace_3618661
  have hstable : (prefixWord ++ tailWord_3618661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618661).length < 2 ^ (prefixWord ++ tailWord_3618661).sum := by decide
  have hdescent : baseEnd_3618661 < baseStart_3618661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618664 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3618664 : Nat := 118140960795 + 3618664 * 2 ^ 59
def prefixEnd_3618664 : Nat := 4983230072969 + 3 ^ 40 * 3618664 * 2
def baseEnd_3618664 : Nat := 619371319707178398052691

theorem tailTrace_3618664 : CollatzResearch.WordTrace tailWord_3618664 prefixEnd_3618664 619371319707178398052691 := by
  unfold tailWord_3618664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65991759481102910726667523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87989012641470547635556697 65991759481102910726667523)
  ·
    refine ⟨98987639221654366090001285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65991759481102910726667523 98987639221654366090001285)
    ·
      refine ⟨18560182354060193641875241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98987639221654366090001285 18560182354060193641875241)
      ·
        refine ⟨13920136765545145231406431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560182354060193641875241 13920136765545145231406431)
        ·
          refine ⟨20880205148317717847109647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13920136765545145231406431 20880205148317717847109647)
          ·
            refine ⟨31320307722476576770664471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20880205148317717847109647 31320307722476576770664471)
            ·
              refine ⟨46980461583714865155996707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31320307722476576770664471 46980461583714865155996707)
              ·
                refine ⟨70470692375572297733995061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46980461583714865155996707 70470692375572297733995061)
                ·
                  refine ⟨6606627410209902912562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70470692375572297733995061 6606627410209902912562037)
                  ·
                    refine ⟨619371319707178398052691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6606627410209902912562037 619371319707178398052691)
                    ·
                      rfl

theorem cell23_3618664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3618664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618664 prefixEnd_3618664 := by exact prefixLift 3618664
  have htrace : WordTrace (prefixWord ++ tailWord_3618664) baseStart_3618664 baseEnd_3618664 := by
    simpa [prefixWord, tailWord_3618664, baseEnd_3618664] using wordTrace_append hprefix tailTrace_3618664
  have hstable : (prefixWord ++ tailWord_3618664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618664).length < 2 ^ (prefixWord ++ tailWord_3618664).sum := by decide
  have hdescent : baseEnd_3618664 < baseStart_3618664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
