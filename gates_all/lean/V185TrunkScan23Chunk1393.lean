import V185TrunkScan23Chunk1392

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8250651 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 1, 2, 2]
def baseStart_8250651 : Nat := 118140960795 + 8250651 * 2 ^ 59
def prefixEnd_8250651 : Nat := 4983230072969 + 3 ^ 40 * 8250651 * 2
def baseEnd_8250651 : Nat := 4236549675498904023718453

theorem tailTrace_8250651 : CollatzResearch.WordTrace tailWord_8250651 prefixEnd_8250651 4236549675498904023718453 := by
  unfold tailWord_8250651
  simp only [CollatzResearch.WordTrace]
  refine ⟨300925964032308000851807807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200617309354872000567871871 300925964032308000851807807)
  ·
    refine ⟨451388946048462001277711711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300925964032308000851807807 451388946048462001277711711)
    ·
      refine ⟨677083419072693001916567567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451388946048462001277711711 677083419072693001916567567)
      ·
        refine ⟨1015625128609039502874851351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677083419072693001916567567 1015625128609039502874851351)
        ·
          refine ⟨1523437692913559254312277027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015625128609039502874851351 1523437692913559254312277027)
          ·
            refine ⟨2285156539370338881468415541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523437692913559254312277027 2285156539370338881468415541)
            ·
              refine ⟨214233425565969270137663957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2285156539370338881468415541 214233425565969270137663957)
              ·
                refine ⟨5021095911702404768851499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214233425565969270137663957 5021095911702404768851499)
                ·
                  refine ⟨7531643867553607153277249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021095911702404768851499 7531643867553607153277249)
                  ·
                    refine ⟨5648732900665205364957937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531643867553607153277249 5648732900665205364957937)
                    ·
                      refine ⟨4236549675498904023718453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648732900665205364957937 4236549675498904023718453)
                      ·
                        rfl

theorem cell23_8250651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 2, 2].length) (baseStart_8250651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250651 prefixEnd_8250651 := by exact prefixLift 8250651
  have htrace : WordTrace (prefixWord ++ tailWord_8250651) baseStart_8250651 baseEnd_8250651 := by
    simpa [prefixWord, tailWord_8250651, baseEnd_8250651] using wordTrace_append hprefix tailTrace_8250651
  have hstable : (prefixWord ++ tailWord_8250651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250651).length < 2 ^ (prefixWord ++ tailWord_8250651).sum := by decide
  have hdescent : baseEnd_8250651 < baseStart_8250651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250680 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_8250680 : Nat := 118140960795 + 8250680 * 2 ^ 59
def prefixEnd_8250680 : Nat := 4983230072969 + 3 ^ 40 * 8250680 * 2
def baseEnd_8250680 : Nat := 4236564566437884410255819

theorem tailTrace_8250680 : CollatzResearch.WordTrace tailWord_8250680 prefixEnd_8250680 4236564566437884410255819 := by
  unfold tailWord_8250680
  simp only [CollatzResearch.WordTrace]
  refine ⟨150463510874601469402306747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200618014499468625869742329 150463510874601469402306747)
  ·
    refine ⟨225695266311902204103460121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150463510874601469402306747 225695266311902204103460121)
    ·
      refine ⟨169271449733926653077595091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225695266311902204103460121 169271449733926653077595091)
      ·
        refine ⟨253907174600889979616392637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169271449733926653077595091 253907174600889979616392637)
        ·
          refine ⟨95215190475333742356147239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253907174600889979616392637 95215190475333742356147239)
          ·
            refine ⟨142822785713000613534220859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95215190475333742356147239 142822785713000613534220859)
            ·
              refine ⟨214234178569500920301331289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142822785713000613534220859 214234178569500920301331289)
              ·
                refine ⟨160675633927125690225998467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214234178569500920301331289 160675633927125690225998467)
                ·
                  refine ⟨241013450890688535338997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160675633927125690225998467 241013450890688535338997701)
                  ·
                    refine ⟨45190022042004100376062069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241013450890688535338997701 45190022042004100376062069)
                    ·
                      refine ⟨4236564566437884410255819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45190022042004100376062069 4236564566437884410255819)
                      ·
                        rfl

theorem cell23_8250680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_8250680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250680 prefixEnd_8250680 := by exact prefixLift 8250680
  have htrace : WordTrace (prefixWord ++ tailWord_8250680) baseStart_8250680 baseEnd_8250680 := by
    simpa [prefixWord, tailWord_8250680, baseEnd_8250680] using wordTrace_append hprefix tailTrace_8250680
  have hstable : (prefixWord ++ tailWord_8250680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250680).length < 2 ^ (prefixWord ++ tailWord_8250680).sum := by decide
  have hdescent : baseEnd_8250680 < baseStart_8250680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250684 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_8250684 : Nat := 118140960795 + 8250684 * 2 ^ 59
def prefixEnd_8250684 : Nat := 4983230072969 + 3 ^ 40 * 8250684 * 2
def baseEnd_8250684 : Nat := 4236566620360502394605801

theorem tailTrace_8250684 : CollatzResearch.WordTrace tailWord_8250684 prefixEnd_8250684 4236566620360502394605801 := by
  unfold tailWord_8250684
  simp only [CollatzResearch.WordTrace]
  refine ⟨150463583820594223743879553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200618111760792298325172737 150463583820594223743879553)
  ·
    refine ⟨112847687865445667807909665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150463583820594223743879553 112847687865445667807909665)
    ·
      refine ⟨84635765899084250855932249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112847687865445667807909665 84635765899084250855932249)
      ·
        refine ⟨63476824424313188141949187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84635765899084250855932249 63476824424313188141949187)
        ·
          refine ⟨95215236636469782212923781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63476824424313188141949187 95215236636469782212923781)
          ·
            refine ⟨17852856869338084164923209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95215236636469782212923781 17852856869338084164923209)
            ·
              refine ⟨13389642652003563123692407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17852856869338084164923209 13389642652003563123692407)
              ·
                refine ⟨20084463978005344685538611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389642652003563123692407 20084463978005344685538611)
                ·
                  refine ⟨30126695967008017028307917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20084463978005344685538611 30126695967008017028307917)
                  ·
                    refine ⟨11297510987628006385615469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30126695967008017028307917 11297510987628006385615469)
                    ·
                      refine ⟨4236566620360502394605801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11297510987628006385615469 4236566620360502394605801)
                      ·
                        rfl

theorem cell23_8250684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_8250684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250684 prefixEnd_8250684 := by exact prefixLift 8250684
  have htrace : WordTrace (prefixWord ++ tailWord_8250684) baseStart_8250684 baseEnd_8250684 := by
    simpa [prefixWord, tailWord_8250684, baseEnd_8250684] using wordTrace_append hprefix tailTrace_8250684
  have hstable : (prefixWord ++ tailWord_8250684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250684).length < 2 ^ (prefixWord ++ tailWord_8250684).sum := by decide
  have hdescent : baseEnd_8250684 < baseStart_8250684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250711 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_8250711 : Nat := 118140960795 + 8250711 * 2 ^ 59
def prefixEnd_8250711 : Nat := 4983230072969 + 3 ^ 40 * 8250711 * 2
def baseEnd_8250711 : Nat := 4236580484338173788968177

theorem tailTrace_8250711 : CollatzResearch.WordTrace tailWord_8250711 prefixEnd_8250711 4236580484338173788968177 := by
  unfold tailWord_8250711
  simp only [CollatzResearch.WordTrace]
  refine ⟨300928152412090631098991987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200618768274727087399327991 300928152412090631098991987)
  ·
    refine ⟨451392228618135946648487981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300928152412090631098991987 451392228618135946648487981)
    ·
      refine ⟨169272085731800979993182993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451392228618135946648487981 169272085731800979993182993)
      ·
        refine ⟨126954064298850734994887245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169272085731800979993182993 126954064298850734994887245)
        ·
          refine ⟨47607774112069025623082717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126954064298850734994887245 47607774112069025623082717)
          ·
            refine ⟨17852915292025884608656019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47607774112069025623082717 17852915292025884608656019)
            ·
              refine ⟨26779372938038826912984029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852915292025884608656019 26779372938038826912984029)
              ·
                refine ⟨10042264851764560092369011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26779372938038826912984029 10042264851764560092369011)
                ·
                  refine ⟨15063397277646840138553517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10042264851764560092369011 15063397277646840138553517)
                  ·
                    refine ⟨5648773979117565051957569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15063397277646840138553517 5648773979117565051957569)
                    ·
                      refine ⟨4236580484338173788968177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648773979117565051957569 4236580484338173788968177)
                      ·
                        rfl

theorem cell23_8250711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_8250711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250711 prefixEnd_8250711 := by exact prefixLift 8250711
  have htrace : WordTrace (prefixWord ++ tailWord_8250711) baseStart_8250711 baseEnd_8250711 := by
    simpa [prefixWord, tailWord_8250711, baseEnd_8250711] using wordTrace_append hprefix tailTrace_8250711
  have hstable : (prefixWord ++ tailWord_8250711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250711).length < 2 ^ (prefixWord ++ tailWord_8250711).sum := by decide
  have hdescent : baseEnd_8250711 < baseStart_8250711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250737 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_8250737 : Nat := 118140960795 + 8250737 * 2 ^ 59
def prefixEnd_8250737 : Nat := 4983230072969 + 3 ^ 40 * 8250737 * 2
def baseEnd_8250737 : Nat := 4236593834835190687243057

theorem tailTrace_8250737 : CollatzResearch.WordTrace tailWord_8250737 prefixEnd_8250737 4236593834835190687243057 := by
  unfold tailWord_8250737
  simp only [CollatzResearch.WordTrace]
  refine ⟨300929100709996437539438465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200619400473330958359625643 300929100709996437539438465)
  ·
    refine ⟨225696825532497328154578849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300929100709996437539438465 225696825532497328154578849)
    ·
      refine ⟨169272619149372996115934137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225696825532497328154578849 169272619149372996115934137)
      ·
        refine ⟨126954464362029747086950603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169272619149372996115934137 126954464362029747086950603)
        ·
          refine ⟨190431696543044620630425905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126954464362029747086950603 190431696543044620630425905)
          ·
            refine ⟨142823772407283465472819429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190431696543044620630425905 142823772407283465472819429)
            ·
              refine ⟨26779457326365649776153643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142823772407283465472819429 26779457326365649776153643)
              ·
                refine ⟨40169185989548474664230465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26779457326365649776153643 40169185989548474664230465)
                ·
                  refine ⟨30126889492161355998172849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40169185989548474664230465 30126889492161355998172849)
                  ·
                    refine ⟨22595167119121016998629637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30126889492161355998172849 22595167119121016998629637)
                    ·
                      refine ⟨4236593834835190687243057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22595167119121016998629637 4236593834835190687243057)
                      ·
                        rfl

theorem cell23_8250737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_8250737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250737 prefixEnd_8250737 := by exact prefixLift 8250737
  have htrace : WordTrace (prefixWord ++ tailWord_8250737) baseStart_8250737 baseEnd_8250737 := by
    simpa [prefixWord, tailWord_8250737, baseEnd_8250737] using wordTrace_append hprefix tailTrace_8250737
  have hstable : (prefixWord ++ tailWord_8250737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250737).length < 2 ^ (prefixWord ++ tailWord_8250737).sum := by decide
  have hdescent : baseEnd_8250737 < baseStart_8250737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250757 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_8250757 : Nat := 118140960795 + 8250757 * 2 ^ 59
def prefixEnd_8250757 : Nat := 4983230072969 + 3 ^ 40 * 8250757 * 2
def baseEnd_8250757 : Nat := 4236604104448280608992965

theorem tailTrace_8250757 : CollatzResearch.WordTrace tailWord_8250757 prefixEnd_8250757 4236604104448280608992965 := by
  unfold tailWord_8250757
  simp only [CollatzResearch.WordTrace]
  refine ⟨300929830169923980955166525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200619886779949320636777683 300929830169923980955166525)
  ·
    refine ⟨112848686313721492858187447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300929830169923980955166525 112848686313721492858187447)
    ·
      refine ⟨169273029470582239287281171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112848686313721492858187447 169273029470582239287281171)
      ·
        refine ⟨253909544205873358930921757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169273029470582239287281171 253909544205873358930921757)
        ·
          refine ⟨95216079077202509599095659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253909544205873358930921757 95216079077202509599095659)
          ·
            refine ⟨142824118615803764398643489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95216079077202509599095659 142824118615803764398643489)
            ·
              refine ⟨107118088961852823298982617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142824118615803764398643489 107118088961852823298982617)
              ·
                refine ⟨80338566721389617474236963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107118088961852823298982617 80338566721389617474236963)
                ·
                  refine ⟨120507850082084426211355445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80338566721389617474236963 120507850082084426211355445)
                  ·
                    refine ⟨11297610945195414957314573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120507850082084426211355445 11297610945195414957314573)
                    ·
                      refine ⟨4236604104448280608992965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11297610945195414957314573 4236604104448280608992965)
                      ·
                        rfl

theorem cell23_8250757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_8250757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250757 prefixEnd_8250757 := by exact prefixLift 8250757
  have htrace : WordTrace (prefixWord ++ tailWord_8250757) baseStart_8250757 baseEnd_8250757 := by
    simpa [prefixWord, tailWord_8250757, baseEnd_8250757] using wordTrace_append hprefix tailTrace_8250757
  have hstable : (prefixWord ++ tailWord_8250757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250757).length < 2 ^ (prefixWord ++ tailWord_8250757).sum := by decide
  have hdescent : baseEnd_8250757 < baseStart_8250757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250777 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_8250777 : Nat := 118140960795 + 8250777 * 2 ^ 59
def prefixEnd_8250777 : Nat := 4983230072969 + 3 ^ 40 * 8250777 * 2
def baseEnd_8250777 : Nat := 1412204791353790176914291

theorem tailTrace_8250777 : CollatzResearch.WordTrace tailWord_8250777 prefixEnd_8250777 1412204791353790176914291 := by
  unfold tailWord_8250777
  simp only [CollatzResearch.WordTrace]
  refine ⟨300930559629851524370894585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200620373086567682913929723 300930559629851524370894585)
  ·
    refine ⟨225697919722388643278170939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300930559629851524370894585 225697919722388643278170939)
    ·
      refine ⟨338546879583582964917256409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225697919722388643278170939 338546879583582964917256409)
      ·
        refine ⟨253910159687687223687942307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338546879583582964917256409 253910159687687223687942307)
        ·
          refine ⟨380865239531530835531913461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253910159687687223687942307 380865239531530835531913461)
          ·
            refine ⟨35706116206081015831116887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380865239531530835531913461 35706116206081015831116887)
            ·
              refine ⟨53559174309121523746675331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35706116206081015831116887 53559174309121523746675331)
              ·
                refine ⟨80338761463682285620012997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53559174309121523746675331 80338761463682285620012997)
                ·
                  refine ⟨15063517774440428553752437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80338761463682285620012997 15063517774440428553752437)
                  ·
                    refine ⟨1412204791353790176914291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15063517774440428553752437 1412204791353790176914291)
                    ·
                      rfl

theorem cell23_8250777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_8250777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250777 prefixEnd_8250777 := by exact prefixLift 8250777
  have htrace : WordTrace (prefixWord ++ tailWord_8250777) baseStart_8250777 baseEnd_8250777 := by
    simpa [prefixWord, tailWord_8250777, baseEnd_8250777] using wordTrace_append hprefix tailTrace_8250777
  have hstable : (prefixWord ++ tailWord_8250777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250777).length < 2 ^ (prefixWord ++ tailWord_8250777).sum := by decide
  have hdescent : baseEnd_8250777 < baseStart_8250777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250784 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2]
def baseStart_8250784 : Nat := 118140960795 + 8250784 * 2 ^ 59
def prefixEnd_8250784 : Nat := 4983230072969 + 3 ^ 40 * 8250784 * 2
def baseEnd_8250784 : Nat := 4236617968425952003355341

theorem tailTrace_8250784 : CollatzResearch.WordTrace tailWord_8250784 prefixEnd_8250784 4236617968425952003355341 := by
  unfold tailWord_8250784
  simp only [CollatzResearch.WordTrace]
  refine ⟨150465407470413082283199703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200620543293884109710932937 150465407470413082283199703)
  ·
    refine ⟨225698111205619623424799555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150465407470413082283199703 225698111205619623424799555)
    ·
      refine ⟨338547166808429435137199333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225698111205619623424799555 338547166808429435137199333)
      ·
        refine ⟨63477593776580519088224875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338547166808429435137199333 63477593776580519088224875)
        ·
          refine ⟨95216390664870778632337313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63477593776580519088224875 95216390664870778632337313)
          ·
            refine ⟨71412292998653083974252985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95216390664870778632337313 71412292998653083974252985)
            ·
              refine ⟨53559219748989812980689739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71412292998653083974252985 53559219748989812980689739)
              ·
                refine ⟨80338829623484719471034609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53559219748989812980689739 80338829623484719471034609)
                ·
                  refine ⟨60254122217613539603275957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80338829623484719471034609 60254122217613539603275957)
                  ·
                    refine ⟨5648823957901269337807121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60254122217613539603275957 5648823957901269337807121)
                    ·
                      refine ⟨4236617968425952003355341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648823957901269337807121 4236617968425952003355341)
                      ·
                        rfl

theorem cell23_8250784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_8250784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250784 prefixEnd_8250784 := by exact prefixLift 8250784
  have htrace : WordTrace (prefixWord ++ tailWord_8250784) baseStart_8250784 baseEnd_8250784 := by
    simpa [prefixWord, tailWord_8250784, baseEnd_8250784] using wordTrace_append hprefix tailTrace_8250784
  have hstable : (prefixWord ++ tailWord_8250784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250784).length < 2 ^ (prefixWord ++ tailWord_8250784).sum := by decide
  have hdescent : baseEnd_8250784 < baseStart_8250784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250787 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_8250787 : Nat := 118140960795 + 8250787 * 2 ^ 59
def prefixEnd_8250787 : Nat := 4983230072969 + 3 ^ 40 * 8250787 * 2
def baseEnd_8250787 : Nat := 4236619508867915491617827

theorem tailTrace_8250787 : CollatzResearch.WordTrace tailWord_8250787 prefixEnd_8250787 4236619508867915491617827 := by
  unfold tailWord_8250787
  simp only [CollatzResearch.WordTrace]
  refine ⟨300930924359815296078758615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200620616239876864052505743 300930924359815296078758615)
  ·
    refine ⟨451396386539722944118137923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300930924359815296078758615 451396386539722944118137923)
    ·
      refine ⟨677094579809584416177206885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451396386539722944118137923 677094579809584416177206885)
      ·
        refine ⟨126955233714297078033226291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677094579809584416177206885 126955233714297078033226291)
        ·
          refine ⟨190432850571445617049839437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126955233714297078033226291 190432850571445617049839437)
          ·
            refine ⟨71412318964292106393689789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190432850571445617049839437 71412318964292106393689789)
            ·
              refine ⟨26779619611609539897633671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71412318964292106393689789 26779619611609539897633671)
              ·
                refine ⟨40169429417414309846450507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26779619611609539897633671 40169429417414309846450507)
                ·
                  refine ⟨60254144126121464769675761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40169429417414309846450507 60254144126121464769675761)
                  ·
                    refine ⟨45190608094591098577256821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60254144126121464769675761 45190608094591098577256821)
                    ·
                      refine ⟨4236619508867915491617827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45190608094591098577256821 4236619508867915491617827)
                      ·
                        rfl

theorem cell23_8250787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_8250787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250787 prefixEnd_8250787 := by exact prefixLift 8250787
  have htrace : WordTrace (prefixWord ++ tailWord_8250787) baseStart_8250787 baseEnd_8250787 := by
    simpa [prefixWord, tailWord_8250787, baseEnd_8250787] using wordTrace_append hprefix tailTrace_8250787
  have hstable : (prefixWord ++ tailWord_8250787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250787).length < 2 ^ (prefixWord ++ tailWord_8250787).sum := by decide
  have hdescent : baseEnd_8250787 < baseStart_8250787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250964 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_8250964 : Nat := 118140960795 + 8250964 * 2 ^ 59
def prefixEnd_8250964 : Nat := 4983230072969 + 3 ^ 40 * 8250964 * 2
def baseEnd_8250964 : Nat := 4236710394943761299104513

theorem tailTrace_8250964 : CollatzResearch.WordTrace tailWord_8250964 prefixEnd_8250964 4236710394943761299104513 := by
  unfold tailWord_8250964
  simp only [CollatzResearch.WordTrace]
  refine ⟨150468690040087027653975973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200624920053449370205301297 150468690040087027653975973)
  ·
    refine ⟨28212879382516317685120495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150468690040087027653975973 28212879382516317685120495)
    ·
      refine ⟨42319319073774476527680743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28212879382516317685120495 42319319073774476527680743)
      ·
        refine ⟨63478978610661714791521115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42319319073774476527680743 63478978610661714791521115)
        ·
          refine ⟨95218467915992572187281673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63478978610661714791521115 95218467915992572187281673)
          ·
            refine ⟨71413850936994429140461255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95218467915992572187281673 71413850936994429140461255)
            ·
              refine ⟨107120776405491643710691883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71413850936994429140461255 107120776405491643710691883)
              ·
                refine ⟨160681164608237465566037825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107120776405491643710691883 160681164608237465566037825)
                ·
                  refine ⟨120510873456178099174528369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160681164608237465566037825 120510873456178099174528369)
                  ·
                    refine ⟨90383155092133574380896277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120510873456178099174528369 90383155092133574380896277)
                    ·
                      refine ⟨4236710394943761299104513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90383155092133574380896277 4236710394943761299104513)
                      ·
                        rfl

theorem cell23_8250964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_8250964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250964 prefixEnd_8250964 := by exact prefixLift 8250964
  have htrace : WordTrace (prefixWord ++ tailWord_8250964) baseStart_8250964 baseEnd_8250964 := by
    simpa [prefixWord, tailWord_8250964, baseEnd_8250964] using wordTrace_append hprefix tailTrace_8250964
  have hstable : (prefixWord ++ tailWord_8250964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250964).length < 2 ^ (prefixWord ++ tailWord_8250964).sum := by decide
  have hdescent : baseEnd_8250964 < baseStart_8250964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251004 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_8251004 : Nat := 118140960795 + 8251004 * 2 ^ 59
def prefixEnd_8251004 : Nat := 4983230072969 + 3 ^ 40 * 8251004 * 2
def baseEnd_8251004 : Nat := 1412243644723313714201443

theorem tailTrace_8251004 : CollatzResearch.WordTrace tailWord_8251004 prefixEnd_8251004 1412243644723313714201443 := by
  unfold tailWord_8251004
  simp only [CollatzResearch.WordTrace]
  refine ⟨150469419500014571069704033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200625892666686094759605377 150469419500014571069704033)
  ·
    refine ⟨112852064625010928302278025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150469419500014571069704033 112852064625010928302278025)
    ·
      refine ⟨84639048468758196226708519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112852064625010928302278025 84639048468758196226708519)
      ·
        refine ⟨126958572703137294340062779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84639048468758196226708519 126958572703137294340062779)
        ·
          refine ⟨190437859054705941510094169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126958572703137294340062779 190437859054705941510094169)
          ·
            refine ⟨142828394291029456132570627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190437859054705941510094169 142828394291029456132570627)
            ·
              refine ⟨214242591436544184198855941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142828394291029456132570627 214242591436544184198855941)
              ·
                refine ⟨40170485894352034537285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214242591436544184198855941 40170485894352034537285489)
                ·
                  refine ⟨30127864420764025902964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40170485894352034537285489 30127864420764025902964117)
                  ·
                    refine ⟨1412243644723313714201443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30127864420764025902964117 1412243644723313714201443)
                    ·
                      rfl

theorem cell23_8251004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_8251004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251004 prefixEnd_8251004 := by exact prefixLift 8251004
  have htrace : WordTrace (prefixWord ++ tailWord_8251004) baseStart_8251004 baseEnd_8251004 := by
    simpa [prefixWord, tailWord_8251004, baseEnd_8251004] using wordTrace_append hprefix tailTrace_8251004
  have hstable : (prefixWord ++ tailWord_8251004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251004).length < 2 ^ (prefixWord ++ tailWord_8251004).sum := by decide
  have hdescent : baseEnd_8251004 < baseStart_8251004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251005 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_8251005 : Nat := 118140960795 + 8251005 * 2 ^ 59
def prefixEnd_8251005 : Nat := 4983230072969 + 3 ^ 40 * 8251005 * 2
def baseEnd_8251005 : Nat := 4236731447650595638691825

theorem tailTrace_8251005 : CollatzResearch.WordTrace tailWord_8251005 prefixEnd_8251005 4236731447650595638691825 := by
  unfold tailWord_8251005
  simp only [CollatzResearch.WordTrace]
  refine ⟨300938875473025519310194469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200625916982017012873462979 300938875473025519310194469)
  ·
    refine ⟨56426039151192284870661463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300938875473025519310194469 56426039151192284870661463)
    ·
      refine ⟨84639058726788427305992195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56426039151192284870661463 84639058726788427305992195)
      ·
        refine ⟨126958588090182640958988293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84639058726788427305992195 126958588090182640958988293)
        ·
          refine ⟨23804735266909245179810305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126958588090182640958988293 23804735266909245179810305)
          ·
            refine ⟨17853551450181933884857729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23804735266909245179810305 17853551450181933884857729)
            ·
              refine ⟨13390163587636450413643297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853551450181933884857729 13390163587636450413643297)
              ·
                refine ⟨10042622690727337810232473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13390163587636450413643297 10042622690727337810232473)
                ·
                  refine ⟨7531967018045503357674355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10042622690727337810232473 7531967018045503357674355)
                  ·
                    refine ⟨11297950527068255036511533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531967018045503357674355 11297950527068255036511533)
                    ·
                      refine ⟨4236731447650595638691825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11297950527068255036511533 4236731447650595638691825)
                      ·
                        rfl

theorem cell23_8251005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_8251005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251005 prefixEnd_8251005 := by exact prefixLift 8251005
  have htrace : WordTrace (prefixWord ++ tailWord_8251005) baseStart_8251005 baseEnd_8251005 := by
    simpa [prefixWord, tailWord_8251005, baseEnd_8251005] using wordTrace_append hprefix tailTrace_8251005
  have hstable : (prefixWord ++ tailWord_8251005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251005).length < 2 ^ (prefixWord ++ tailWord_8251005).sum := by decide
  have hdescent : baseEnd_8251005 < baseStart_8251005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 4, 2]
def baseStart_8251011 : Nat := 118140960795 + 8251011 * 2 ^ 59
def prefixEnd_8251011 : Nat := 4983230072969 + 3 ^ 40 * 8251011 * 2
def baseEnd_8251011 : Nat := 4236734528534522615216797

theorem tailTrace_8251011 : CollatzResearch.WordTrace tailWord_8251011 prefixEnd_8251011 4236734528534522615216797 := by
  unfold tailWord_8251011
  simp only [CollatzResearch.WordTrace]
  refine ⟨300939094311003782334912887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200626062874002521556608591 300939094311003782334912887)
  ·
    refine ⟨451408641466505673502369331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300939094311003782334912887 451408641466505673502369331)
    ·
      refine ⟨677112962199758510253553997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451408641466505673502369331 677112962199758510253553997)
      ·
        refine ⟨253917360824909441345082749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677112962199758510253553997 253917360824909441345082749)
        ·
          refine ⟨95219010309341040504406031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253917360824909441345082749 95219010309341040504406031)
          ·
            refine ⟨142828515464011560756609047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95219010309341040504406031 142828515464011560756609047)
            ·
              refine ⟨214242773196017341134913571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142828515464011560756609047 214242773196017341134913571)
              ·
                refine ⟨321364159794026011702370357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214242773196017341134913571 321364159794026011702370357)
                ·
                  refine ⟨30127889980689938597097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321364159794026011702370357 30127889980689938597097221)
                  ·
                    refine ⟨5648979371379363486955729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30127889980689938597097221 5648979371379363486955729)
                    ·
                      refine ⟨4236734528534522615216797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648979371379363486955729 4236734528534522615216797)
                      ·
                        rfl

theorem cell23_8251011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_8251011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251011 prefixEnd_8251011 := by exact prefixLift 8251011
  have htrace : WordTrace (prefixWord ++ tailWord_8251011) baseStart_8251011 baseEnd_8251011 := by
    simpa [prefixWord, tailWord_8251011, baseEnd_8251011] using wordTrace_append hprefix tailTrace_8251011
  have hstable : (prefixWord ++ tailWord_8251011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251011).length < 2 ^ (prefixWord ++ tailWord_8251011).sum := by decide
  have hdescent : baseEnd_8251011 < baseStart_8251011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251068 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 5]
def baseStart_8251068 : Nat := 118140960795 + 8251068 * 2 ^ 59
def prefixEnd_8251068 : Nat := 4983230072969 + 3 ^ 40 * 8251068 * 2
def baseEnd_8251068 : Nat := 470751532992425432467115

theorem tailTrace_8251068 : CollatzResearch.WordTrace tailWord_8251068 prefixEnd_8251068 470751532992425432467115 := by
  unfold tailWord_8251068
  simp only [CollatzResearch.WordTrace]
  refine ⟨150470586635898640534868929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200627448847864854046491905 150470586635898640534868929)
  ·
    refine ⟨112852939976923980401151697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150470586635898640534868929 112852939976923980401151697)
    ·
      refine ⟨84639704982692985300863773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112852939976923980401151697 84639704982692985300863773)
      ·
        refine ⟨31739889368509869487823915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84639704982692985300863773 31739889368509869487823915)
        ·
          refine ⟨47609834052764804231735873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31739889368509869487823915 47609834052764804231735873)
          ·
            refine ⟨35707375539573603173801905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47609834052764804231735873 35707375539573603173801905)
            ·
              refine ⟨26780531654680202380351429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35707375539573603173801905 26780531654680202380351429)
              ·
                refine ⟨5021349685252537946315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26780531654680202380351429 5021349685252537946315893)
                ·
                  refine ⟨470751532992425432467115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021349685252537946315893 470751532992425432467115)
                  ·
                    rfl

theorem cell23_8251068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_8251068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251068 prefixEnd_8251068 := by exact prefixLift 8251068
  have htrace : WordTrace (prefixWord ++ tailWord_8251068) baseStart_8251068 baseEnd_8251068 := by
    simpa [prefixWord, tailWord_8251068, baseEnd_8251068] using wordTrace_append hprefix tailTrace_8251068
  have hstable : (prefixWord ++ tailWord_8251068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251068).length < 2 ^ (prefixWord ++ tailWord_8251068).sum := by decide
  have hdescent : baseEnd_8251068 < baseStart_8251068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251118 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_8251118 : Nat := 118140960795 + 8251118 * 2 ^ 59
def prefixEnd_8251118 : Nat := 4983230072969 + 3 ^ 40 * 8251118 * 2
def baseEnd_8251118 : Nat := 4236789470964553696578805

theorem tailTrace_8251118 : CollatzResearch.WordTrace tailWord_8251118 prefixEnd_8251118 4236789470964553696578805 := by
  unfold tailWord_8251118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617874615202017451132251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200628664614410759739372005 37617874615202017451132251)
  ·
    refine ⟨56426811922803026176698377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617874615202017451132251 56426811922803026176698377)
    ·
      refine ⟨42320108942102269632523783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56426811922803026176698377 42320108942102269632523783)
      ·
        refine ⟨63480163413153404448785675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42320108942102269632523783 63480163413153404448785675)
        ·
          refine ⟨95220245119730106673178513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63480163413153404448785675 95220245119730106673178513)
          ·
            refine ⟨71415183839797580004883885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95220245119730106673178513 71415183839797580004883885)
            ·
              refine ⟨26780693939924092501831457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71415183839797580004883885 26780693939924092501831457)
              ·
                refine ⟨20085520454943069376373593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26780693939924092501831457 20085520454943069376373593)
                ·
                  refine ⟨15064140341207302032280195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20085520454943069376373593 15064140341207302032280195)
                  ·
                    refine ⟨22596210511810953048420293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15064140341207302032280195 22596210511810953048420293)
                    ·
                      refine ⟨4236789470964553696578805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22596210511810953048420293 4236789470964553696578805)
                      ·
                        rfl

theorem cell23_8251118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_8251118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251118 prefixEnd_8251118 := by exact prefixLift 8251118
  have htrace : WordTrace (prefixWord ++ tailWord_8251118) baseStart_8251118 baseEnd_8251118 := by
    simpa [prefixWord, tailWord_8251118, baseEnd_8251118] using wordTrace_append hprefix tailTrace_8251118
  have hstable : (prefixWord ++ tailWord_8251118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251118).length < 2 ^ (prefixWord ++ tailWord_8251118).sum := by decide
  have hdescent : baseEnd_8251118 < baseStart_8251118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251208 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_8251208 : Nat := 118140960795 + 8251208 * 2 ^ 59
def prefixEnd_8251208 : Nat := 4983230072969 + 3 ^ 40 * 8251208 * 2
def baseEnd_8251208 : Nat := 4236835684223458344453391

theorem tailTrace_8251208 : CollatzResearch.WordTrace tailWord_8251208 prefixEnd_8251208 4236835684223458344453391 := by
  unfold tailWord_8251208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150473139745645042489917139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200630852994193389986556185 150473139745645042489917139)
  ·
    refine ⟨225709709618467563734875709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150473139745645042489917139 225709709618467563734875709)
    ·
      refine ⟨84641141106925336400578391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225709709618467563734875709 84641141106925336400578391)
      ·
        refine ⟨126961711660388004600867587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84641141106925336400578391 126961711660388004600867587)
        ·
          refine ⟨190442567490582006901301381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126961711660388004600867587 190442567490582006901301381)
          ·
            refine ⟨35707981404484126293994009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190442567490582006901301381 35707981404484126293994009)
            ·
              refine ⟨26780986053363094720495507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35707981404484126293994009 26780986053363094720495507)
              ·
                refine ⟨40171479080044642080743261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26780986053363094720495507 40171479080044642080743261)
                ·
                  refine ⟨15064304655016740780278723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40171479080044642080743261 15064304655016740780278723)
                  ·
                    refine ⟨22596456982525111170418085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15064304655016740780278723 22596456982525111170418085)
                    ·
                      refine ⟨4236835684223458344453391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22596456982525111170418085 4236835684223458344453391)
                      ·
                        rfl

theorem cell23_8251208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_8251208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251208 prefixEnd_8251208 := by exact prefixLift 8251208
  have htrace : WordTrace (prefixWord ++ tailWord_8251208) baseStart_8251208 baseEnd_8251208 := by
    simpa [prefixWord, tailWord_8251208, baseEnd_8251208] using wordTrace_append hprefix tailTrace_8251208
  have hstable : (prefixWord ++ tailWord_8251208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251208).length < 2 ^ (prefixWord ++ tailWord_8251208).sum := by decide
  have hdescent : baseEnd_8251208 < baseStart_8251208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251218 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_8251218 : Nat := 118140960795 + 8251218 * 2 ^ 59
def prefixEnd_8251218 : Nat := 4983230072969 + 3 ^ 40 * 8251218 * 2
def baseEnd_8251218 : Nat := 1412280273010001101776115

theorem tailTrace_8251218 : CollatzResearch.WordTrace tailWord_8251218 prefixEnd_8251218 1412280273010001101776115 := by
  unfold tailWord_8251218
  simp only [CollatzResearch.WordTrace]
  refine ⟨75236661055313464171924577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200631096147502571125132205 75236661055313464171924577)
  ·
    refine ⟨56427495791485098128943433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75236661055313464171924577 56427495791485098128943433)
    ·
      refine ⟨42320621843613823596707575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56427495791485098128943433 42320621843613823596707575)
      ·
        refine ⟨63480932765420735395061363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42320621843613823596707575 63480932765420735395061363)
        ·
          refine ⟨95221399148131103092592045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63480932765420735395061363 95221399148131103092592045)
          ·
            refine ⟨35708024680549163659722017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95221399148131103092592045 35708024680549163659722017)
            ·
              refine ⟨26781018510411872744791513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35708024680549163659722017 26781018510411872744791513)
              ·
                refine ⟨20085763882808904558593635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26781018510411872744791513 20085763882808904558593635)
                ·
                  refine ⟨30128645824213356837890453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20085763882808904558593635 30128645824213356837890453)
                  ·
                    refine ⟨1412280273010001101776115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30128645824213356837890453 1412280273010001101776115)
                    ·
                      rfl

theorem cell23_8251218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_8251218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251218 prefixEnd_8251218 := by exact prefixLift 8251218
  have htrace : WordTrace (prefixWord ++ tailWord_8251218) baseStart_8251218 baseEnd_8251218 := by
    simpa [prefixWord, tailWord_8251218, baseEnd_8251218] using wordTrace_append hprefix tailTrace_8251218
  have hstable : (prefixWord ++ tailWord_8251218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251218).length < 2 ^ (prefixWord ++ tailWord_8251218).sum := by decide
  have hdescent : baseEnd_8251218 < baseStart_8251218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251225 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 5, 2, 2]
def baseStart_8251225 : Nat := 118140960795 + 8251225 * 2 ^ 59
def prefixEnd_8251225 : Nat := 4983230072969 + 3 ^ 40 * 8251225 * 2
def baseEnd_8251225 : Nat := 4236844413394584777940813

theorem tailTrace_8251225 : CollatzResearch.WordTrace tailWord_8251225 prefixEnd_8251225 4236844413394584777940813 := by
  unfold tailWord_8251225
  simp only [CollatzResearch.WordTrace]
  refine ⟨300946899532228496883203129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200631266354818997922135419 300946899532228496883203129)
  ·
    refine ⟨225710174649171372662402347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300946899532228496883203129 225710174649171372662402347)
    ·
      refine ⟨338565261973757058993603521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225710174649171372662402347 338565261973757058993603521)
      ·
        refine ⟨253923946480317794245202641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338565261973757058993603521 253923946480317794245202641)
        ·
          refine ⟨190442959860238345683901981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253923946480317794245202641 190442959860238345683901981)
          ·
            refine ⟨71416109947589379631463243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190442959860238345683901981 71416109947589379631463243)
            ·
              refine ⟨107124164921384069447194865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71416109947589379631463243 107124164921384069447194865)
              ·
                refine ⟨80343123691038052085396149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107124164921384069447194865 80343123691038052085396149)
                ·
                  refine ⟨7532167846034817383005889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80343123691038052085396149 7532167846034817383005889)
                  ·
                    refine ⟨5649125884526113037254417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532167846034817383005889 5649125884526113037254417)
                    ·
                      refine ⟨4236844413394584777940813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649125884526113037254417 4236844413394584777940813)
                      ·
                        rfl

theorem cell23_8251225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_8251225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251225 prefixEnd_8251225 := by exact prefixLift 8251225
  have htrace : WordTrace (prefixWord ++ tailWord_8251225) baseStart_8251225 baseEnd_8251225 := by
    simpa [prefixWord, tailWord_8251225, baseEnd_8251225] using wordTrace_append hprefix tailTrace_8251225
  have hstable : (prefixWord ++ tailWord_8251225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251225).length < 2 ^ (prefixWord ++ tailWord_8251225).sum := by decide
  have hdescent : baseEnd_8251225 < baseStart_8251225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251231 : List Nat := [1, 1, 2, 3, 1, 5, 10]
def baseStart_8251231 : Nat := 118140960795 + 8251231 * 2 ^ 59
def prefixEnd_8251231 : Nat := 4983230072969 + 3 ^ 40 * 8251231 * 2
def baseEnd_8251231 : Nat := 52306759188623601906985

theorem tailTrace_8251231 : CollatzResearch.WordTrace tailWord_8251231 prefixEnd_8251231 52306759188623601906985 := by
  unfold tailWord_8251231
  simp only [CollatzResearch.WordTrace]
  refine ⟨300947118370206759907921547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200631412246804506605281031 300947118370206759907921547)
  ·
    refine ⟨451420677555310139861882321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300947118370206759907921547 451420677555310139861882321)
    ·
      refine ⟨338565508166482604896411741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451420677555310139861882321 338565508166482604896411741)
      ·
        refine ⟨126962065562430976836154403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338565508166482604896411741 126962065562430976836154403)
        ·
          refine ⟨190443098343646465254231605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126962065562430976836154403 190443098343646465254231605)
          ·
            refine ⟨17854040469716856117584213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190443098343646465254231605 17854040469716856117584213)
            ·
              refine ⟨52306759188623601906985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17854040469716856117584213 52306759188623601906985)
              ·
                rfl

theorem cell23_8251231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 10].length) (baseStart_8251231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251231 prefixEnd_8251231 := by exact prefixLift 8251231
  have htrace : WordTrace (prefixWord ++ tailWord_8251231) baseStart_8251231 baseEnd_8251231 := by
    simpa [prefixWord, tailWord_8251231, baseEnd_8251231] using wordTrace_append hprefix tailTrace_8251231
  have hstable : (prefixWord ++ tailWord_8251231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251231).length < 2 ^ (prefixWord ++ tailWord_8251231).sum := by decide
  have hdescent : baseEnd_8251231 < baseStart_8251231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251235 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 4, 4]
def baseStart_8251235 : Nat := 118140960795 + 8251235 * 2 ^ 59
def prefixEnd_8251235 : Nat := 4983230072969 + 3 ^ 40 * 8251235 * 2
def baseEnd_8251235 : Nat := 1412283182733709912938589

theorem tailTrace_8251235 : CollatzResearch.WordTrace tailWord_8251235 prefixEnd_8251235 1412283182733709912938589 := by
  unfold tailWord_8251235
  simp only [CollatzResearch.WordTrace]
  refine ⟨300947264262192268591067159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200631509508128179060711439 300947264262192268591067159)
  ·
    refine ⟨451420896393288402886600739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300947264262192268591067159 451420896393288402886600739)
    ·
      refine ⟨677131344589932604329901109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451420896393288402886600739 677131344589932604329901109)
      ·
        refine ⟨63481063555306181655928229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 677131344589932604329901109 63481063555306181655928229)
        ·
          refine ⟨11902699416619909060486543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63481063555306181655928229 11902699416619909060486543)
          ·
            refine ⟨17854049124929863590729815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902699416619909060486543 17854049124929863590729815)
            ·
              refine ⟨26781073687394795386094723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854049124929863590729815 26781073687394795386094723)
              ·
                refine ⟨40171610531092193079142085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26781073687394795386094723 40171610531092193079142085)
                ·
                  refine ⟨7532176974579786202339141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40171610531092193079142085 7532176974579786202339141)
                  ·
                    refine ⟨1412283182733709912938589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532176974579786202339141 1412283182733709912938589)
                    ·
                      rfl

theorem cell23_8251235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 4].length) (baseStart_8251235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251235 prefixEnd_8251235 := by exact prefixLift 8251235
  have htrace : WordTrace (prefixWord ++ tailWord_8251235) baseStart_8251235 baseEnd_8251235 := by
    simpa [prefixWord, tailWord_8251235, baseEnd_8251235] using wordTrace_append hprefix tailTrace_8251235
  have hstable : (prefixWord ++ tailWord_8251235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251235).length < 2 ^ (prefixWord ++ tailWord_8251235).sum := by decide
  have hdescent : baseEnd_8251235 < baseStart_8251235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251265 : List Nat := [1, 2, 4, 4, 1, 1, 1, 9]
def baseStart_8251265 : Nat := 118140960795 + 8251265 * 2 ^ 59
def prefixEnd_8251265 : Nat := 4983230072969 + 3 ^ 40 * 8251265 * 2
def baseEnd_8251265 : Nat := 156920924171139430423727

theorem tailTrace_8251265 : CollatzResearch.WordTrace tailWord_8251265 prefixEnd_8251265 156920924171139430423727 := by
  unfold tailWord_8251265
  simp only [CollatzResearch.WordTrace]
  refine ⟨300948358452083583714659249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200632238968055722476439499 300948358452083583714659249)
  ·
    refine ⟨225711268839062687785994437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300948358452083583714659249 225711268839062687785994437)
    ·
      refine ⟨42320862907324253959873957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225711268839062687785994437 42320862907324253959873957)
      ·
        refine ⟨7935161795123297617476367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42320862907324253959873957 7935161795123297617476367)
        ·
          refine ⟨11902742692684946426214551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935161795123297617476367 11902742692684946426214551)
          ·
            refine ⟨17854114039027419639321827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902742692684946426214551 17854114039027419639321827)
            ·
              refine ⟨26781171058541129458982741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854114039027419639321827 26781171058541129458982741)
              ·
                refine ⟨156920924171139430423727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26781171058541129458982741 156920924171139430423727)
                ·
                  rfl

theorem cell23_8251265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 9].length) (baseStart_8251265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251265 prefixEnd_8251265 := by exact prefixLift 8251265
  have htrace : WordTrace (prefixWord ++ tailWord_8251265) baseStart_8251265 baseEnd_8251265 := by
    simpa [prefixWord, tailWord_8251265, baseEnd_8251265] using wordTrace_append hprefix tailTrace_8251265
  have hstable : (prefixWord ++ tailWord_8251265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251265).length < 2 ^ (prefixWord ++ tailWord_8251265).sum := by decide
  have hdescent : baseEnd_8251265 < baseStart_8251265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251292 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_8251292 : Nat := 118140960795 + 8251292 * 2 ^ 59
def prefixEnd_8251292 : Nat := 4983230072969 + 3 ^ 40 * 8251292 * 2
def baseEnd_8251292 : Nat := 4236878816598436015803005

theorem tailTrace_8251292 : CollatzResearch.WordTrace tailWord_8251292 prefixEnd_8251292 4236878816598436015803005 := by
  unfold tailWord_8251292
  simp only [CollatzResearch.WordTrace]
  refine ⟨150474671611492883662946065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200632895481990511550594753 150474671611492883662946065)
  ·
    refine ⟨112856003708619662747209549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150474671611492883662946065 112856003708619662747209549)
    ·
      refine ⟨42321001390732373530203581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112856003708619662747209549 42321001390732373530203581)
      ·
        refine ⟨15870375521524640073826343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42321001390732373530203581 15870375521524640073826343)
        ·
          refine ⟨23805563282286960110739515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870375521524640073826343 23805563282286960110739515)
          ·
            refine ⟨35708344923430440166109273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23805563282286960110739515 35708344923430440166109273)
            ·
              refine ⟨26781258692572830124581955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35708344923430440166109273 26781258692572830124581955)
              ·
                refine ⟨40171888038859245186872933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26781258692572830124581955 40171888038859245186872933)
                ·
                  refine ⟨7532229007286108472538675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40171888038859245186872933 7532229007286108472538675)
                  ·
                    refine ⟨11298343510929162708808013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7532229007286108472538675 11298343510929162708808013)
                    ·
                      refine ⟨4236878816598436015803005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11298343510929162708808013 4236878816598436015803005)
                      ·
                        rfl

theorem cell23_8251292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_8251292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251292 prefixEnd_8251292 := by exact prefixLift 8251292
  have htrace : WordTrace (prefixWord ++ tailWord_8251292) baseStart_8251292 baseEnd_8251292 := by
    simpa [prefixWord, tailWord_8251292, baseEnd_8251292] using wordTrace_append hprefix tailTrace_8251292
  have hstable : (prefixWord ++ tailWord_8251292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251292).length < 2 ^ (prefixWord ++ tailWord_8251292).sum := by decide
  have hdescent : baseEnd_8251292 < baseStart_8251292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251315 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 4, 2]
def baseStart_8251315 : Nat := 118140960795 + 8251315 * 2 ^ 59
def prefixEnd_8251315 : Nat := 4983230072969 + 3 ^ 40 * 8251315 * 2
def baseEnd_8251315 : Nat := 4236890626653489425815399

theorem tailTrace_8251315 : CollatzResearch.WordTrace tailWord_8251315 prefixEnd_8251315 4236890626653489425815399 := by
  unfold tailWord_8251315
  simp only [CollatzResearch.WordTrace]
  refine ⟨300950182101902442253979399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200633454734601628169319599 300950182101902442253979399)
  ·
    refine ⟨451425273152853663380969099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300950182101902442253979399 451425273152853663380969099)
    ·
      refine ⟨677137909729280495071453649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451425273152853663380969099 677137909729280495071453649)
      ·
        refine ⟨507853432296960371303590237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677137909729280495071453649 507853432296960371303590237)
        ·
          refine ⟨190445037111360139238846339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507853432296960371303590237 190445037111360139238846339)
          ·
            refine ⟨285667555667040208858269509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190445037111360139238846339 285667555667040208858269509)
            ·
              refine ⟨53562666687570039160925533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285667555667040208858269509 53562666687570039160925533)
              ·
                refine ⟨20086000007838764685347075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53562666687570039160925533 20086000007838764685347075)
                ·
                  refine ⟨30129000011758147028020613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20086000007838764685347075 30129000011758147028020613)
                  ·
                    refine ⟨5649187502204652567753865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30129000011758147028020613 5649187502204652567753865)
                    ·
                      refine ⟨4236890626653489425815399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649187502204652567753865 4236890626653489425815399)
                      ·
                        rfl

theorem cell23_8251315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4, 2].length) (baseStart_8251315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251315 prefixEnd_8251315 := by exact prefixLift 8251315
  have htrace : WordTrace (prefixWord ++ tailWord_8251315) baseStart_8251315 baseEnd_8251315 := by
    simpa [prefixWord, tailWord_8251315, baseEnd_8251315] using wordTrace_append hprefix tailTrace_8251315
  have hstable : (prefixWord ++ tailWord_8251315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251315).length < 2 ^ (prefixWord ++ tailWord_8251315).sum := by decide
  have hdescent : baseEnd_8251315 < baseStart_8251315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251349 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_8251349 : Nat := 118140960795 + 8251349 * 2 ^ 59
def prefixEnd_8251349 : Nat := 4983230072969 + 3 ^ 40 * 8251349 * 2
def baseEnd_8251349 : Nat := 4236908084995742292790243

theorem tailTrace_8251349 : CollatzResearch.WordTrace tailWord_8251349 prefixEnd_8251349 4236908084995742292790243 := by
  unfold tailWord_8251349
  simp only [CollatzResearch.WordTrace]
  refine ⟨300951422183779266060717101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200634281455852844040478067 300951422183779266060717101)
  ·
    refine ⟨112856783318917224772768913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300951422183779266060717101 112856783318917224772768913)
    ·
      refine ⟨84642587489187918579576685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112856783318917224772768913 84642587489187918579576685)
      ·
        refine ⟨31740970308445469467341257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84642587489187918579576685 31740970308445469467341257)
        ·
          refine ⟨23805727731334102100505943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31740970308445469467341257 23805727731334102100505943)
          ·
            refine ⟨35708591597001153150758915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23805727731334102100505943 35708591597001153150758915)
            ·
              refine ⟨53562887395501729726138373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35708591597001153150758915 53562887395501729726138373)
              ·
                refine ⟨10043041386656574323650945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53562887395501729726138373 10043041386656574323650945)
                ·
                  refine ⟨7532281039992430742738209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043041386656574323650945 7532281039992430742738209)
                  ·
                    refine ⟨5649210779994323057053657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532281039992430742738209 5649210779994323057053657)
                    ·
                      refine ⟨4236908084995742292790243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649210779994323057053657 4236908084995742292790243)
                      ·
                        rfl

theorem cell23_8251349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_8251349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251349 prefixEnd_8251349 := by exact prefixLift 8251349
  have htrace : WordTrace (prefixWord ++ tailWord_8251349) baseStart_8251349 baseEnd_8251349 := by
    simpa [prefixWord, tailWord_8251349, baseEnd_8251349] using wordTrace_append hprefix tailTrace_8251349
  have hstable : (prefixWord ++ tailWord_8251349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251349).length < 2 ^ (prefixWord ++ tailWord_8251349).sum := by decide
  have hdescent : baseEnd_8251349 < baseStart_8251349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251368 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_8251368 : Nat := 118140960795 + 8251368 * 2 ^ 59
def prefixEnd_8251368 : Nat := 4983230072969 + 3 ^ 40 * 8251368 * 2
def baseEnd_8251368 : Nat := 1412305947042725906150885

theorem tailTrace_8251368 : CollatzResearch.WordTrace tailWord_8251368 prefixEnd_8251368 1412305947042725906150885 := by
  unfold tailWord_8251368
  simp only [CollatzResearch.WordTrace]
  refine ⟨150476057585355216152829379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200634743447140288203772505 150476057585355216152829379)
  ·
    refine ⟨225714086378032824229244069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150476057585355216152829379 225714086378032824229244069)
    ·
      refine ⟨42321391195881154542983263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225714086378032824229244069 42321391195881154542983263)
      ·
        refine ⟨63482086793821731814474895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42321391195881154542983263 63482086793821731814474895)
        ·
          refine ⟨95223130190732597721712343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63482086793821731814474895 95223130190732597721712343)
          ·
            refine ⟨142834695286098896582568515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95223130190732597721712343 142834695286098896582568515)
            ·
              refine ⟨214252042929148344873852773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142834695286098896582568515 214252042929148344873852773)
              ·
                refine ⟨40172258049215314663847395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214252042929148344873852773 40172258049215314663847395)
                ·
                  refine ⟨60258387073822971995771093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40172258049215314663847395 60258387073822971995771093)
                  ·
                    refine ⟨1412305947042725906150885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60258387073822971995771093 1412305947042725906150885)
                    ·
                      rfl

theorem cell23_8251368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_8251368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251368 prefixEnd_8251368 := by exact prefixLift 8251368
  have htrace : WordTrace (prefixWord ++ tailWord_8251368) baseStart_8251368 baseEnd_8251368 := by
    simpa [prefixWord, tailWord_8251368, baseEnd_8251368] using wordTrace_append hprefix tailTrace_8251368
  have hstable : (prefixWord ++ tailWord_8251368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251368).length < 2 ^ (prefixWord ++ tailWord_8251368).sum := by decide
  have hdescent : baseEnd_8251368 < baseStart_8251368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251375 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 5, 2]
def baseStart_8251375 : Nat := 118140960795 + 8251375 * 2 ^ 59
def prefixEnd_8251375 : Nat := 4983230072969 + 3 ^ 40 * 8251375 * 2
def baseEnd_8251375 : Nat := 4236921435492759191065123

theorem tailTrace_8251375 : CollatzResearch.WordTrace tailWord_8251375 prefixEnd_8251375 4236921435492759191065123 := by
  unfold tailWord_8251375
  simp only [CollatzResearch.WordTrace]
  refine ⟨300952370481685072501163579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200634913654456715000775719 300952370481685072501163579)
  ·
    refine ⟨451428555722527608751745369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300952370481685072501163579 451428555722527608751745369)
    ·
      refine ⟨338571416791895706563809027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451428555722527608751745369 338571416791895706563809027)
      ·
        refine ⟨507857125187843559845713541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338571416791895706563809027 507857125187843559845713541)
        ·
          refine ⟨95223210972720667471071289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507857125187843559845713541 95223210972720667471071289)
          ·
            refine ⟨71417408229540500603303467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95223210972720667471071289 71417408229540500603303467)
            ·
              refine ⟨107126112344310750904955201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71417408229540500603303467 107126112344310750904955201)
              ·
                refine ⟨80344584258233063178716401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107126112344310750904955201 80344584258233063178716401)
                ·
                  refine ⟨60258438193674797384037301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80344584258233063178716401 60258438193674797384037301)
                  ·
                    refine ⟨5649228580657012254753497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60258438193674797384037301 5649228580657012254753497)
                    ·
                      refine ⟨4236921435492759191065123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649228580657012254753497 4236921435492759191065123)
                      ·
                        rfl

theorem cell23_8251375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5, 2].length) (baseStart_8251375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251375 prefixEnd_8251375 := by exact prefixLift 8251375
  have htrace : WordTrace (prefixWord ++ tailWord_8251375) baseStart_8251375 baseEnd_8251375 := by
    simpa [prefixWord, tailWord_8251375, baseEnd_8251375] using wordTrace_append hprefix tailTrace_8251375
  have hstable : (prefixWord ++ tailWord_8251375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251375).length < 2 ^ (prefixWord ++ tailWord_8251375).sum := by decide
  have hdescent : baseEnd_8251375 < baseStart_8251375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251385 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_8251385 : Nat := 118140960795 + 8251385 * 2 ^ 59
def prefixEnd_8251385 : Nat := 4983230072969 + 3 ^ 40 * 8251385 * 2
def baseEnd_8251385 : Nat := 1412308856766434717313359

theorem tailTrace_8251385 : CollatzResearch.WordTrace tailWord_8251385 prefixEnd_8251385 1412308856766434717313359 := by
  unfold tailWord_8251385
  simp only [CollatzResearch.WordTrace]
  refine ⟨300952735211648844209027609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200635156807765896139351739 300952735211648844209027609)
  ·
    refine ⟨225714551408736633156770707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300952735211648844209027609 225714551408736633156770707)
    ·
      refine ⟨338571827113104949735156061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225714551408736633156770707 338571827113104949735156061)
      ·
        refine ⟨126964435167414356150683523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338571827113104949735156061 126964435167414356150683523)
        ·
          refine ⟨190446652751121534226025285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126964435167414356150683523 190446652751121534226025285)
          ·
            refine ⟨35708747390835287667379741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190446652751121534226025285 35708747390835287667379741)
            ·
              refine ⟨13390780271563232875267403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35708747390835287667379741 13390780271563232875267403)
              ·
                refine ⟨20086170407344849312901105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13390780271563232875267403 20086170407344849312901105)
                ·
                  refine ⟨15064627805508636984675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20086170407344849312901105 15064627805508636984675829)
                  ·
                    refine ⟨1412308856766434717313359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15064627805508636984675829 1412308856766434717313359)
                    ·
                      rfl

theorem cell23_8251385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_8251385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251385 prefixEnd_8251385 := by exact prefixLift 8251385
  have htrace : WordTrace (prefixWord ++ tailWord_8251385) baseStart_8251385 baseEnd_8251385 := by
    simpa [prefixWord, tailWord_8251385, baseEnd_8251385] using wordTrace_append hprefix tailTrace_8251385
  have hstable : (prefixWord ++ tailWord_8251385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251385).length < 2 ^ (prefixWord ++ tailWord_8251385).sum := by decide
  have hdescent : baseEnd_8251385 < baseStart_8251385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251462 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_8251462 : Nat := 118140960795 + 8251462 * 2 ^ 59
def prefixEnd_8251462 : Nat := 4983230072969 + 3 ^ 40 * 8251462 * 2
def baseEnd_8251462 : Nat := 470774012034411150075247

theorem tailTrace_8251462 : CollatzResearch.WordTrace tailWord_8251462 prefixEnd_8251462 470774012034411150075247 := by
  unfold tailWord_8251462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404860738511558948736895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200637029088246590906387093 9404860738511558948736895)
  ·
    refine ⟨14107291107767338423105343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404860738511558948736895 14107291107767338423105343)
    ·
      refine ⟨21160936661651007634658015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107291107767338423105343 21160936661651007634658015)
      ·
        refine ⟨31741404992476511451987023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21160936661651007634658015 31741404992476511451987023)
        ·
          refine ⟨47612107488714767177980535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31741404992476511451987023 47612107488714767177980535)
          ·
            refine ⟨71418161233072150766970803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47612107488714767177980535 71418161233072150766970803)
            ·
              refine ⟨107127241849608226150456205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71418161233072150766970803 107127241849608226150456205)
              ·
                refine ⟨40172715693603084806421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107127241849608226150456205 40172715693603084806421077)
                ·
                  refine ⟨470774012034411150075247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40172715693603084806421077 470774012034411150075247)
                  ·
                    rfl

theorem cell23_8251462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_8251462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251462 prefixEnd_8251462 := by exact prefixLift 8251462
  have htrace : WordTrace (prefixWord ++ tailWord_8251462) baseStart_8251462 baseEnd_8251462 := by
    simpa [prefixWord, tailWord_8251462, baseEnd_8251462] using wordTrace_append hprefix tailTrace_8251462
  have hstable : (prefixWord ++ tailWord_8251462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251462).length < 2 ^ (prefixWord ++ tailWord_8251462).sum := by decide
  have hdescent : baseEnd_8251462 < baseStart_8251462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251482 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_8251482 : Nat := 118140960795 + 8251482 * 2 ^ 59
def prefixEnd_8251482 : Nat := 4983230072969 + 3 ^ 40 * 8251482 * 2
def baseEnd_8251482 : Nat := 4236976377922790272427131

theorem tailTrace_8251482 : CollatzResearch.WordTrace tailWord_8251482 prefixEnd_8251482 4236976377922790272427131 := by
  unfold tailWord_8251482
  simp only [CollatzResearch.WordTrace]
  refine ⟨75239068273074357443827175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200637515394864953183539133 75239068273074357443827175)
  ·
    refine ⟨112858602409611536165740763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75239068273074357443827175 112858602409611536165740763)
    ·
      refine ⟨169287903614417304248611145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112858602409611536165740763 169287903614417304248611145)
      ·
        refine ⟨126965927710812978186458359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169287903614417304248611145 126965927710812978186458359)
        ·
          refine ⟨190448891566219467279687539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126965927710812978186458359 190448891566219467279687539)
          ·
            refine ⟨285673337349329200919531309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190448891566219467279687539 285673337349329200919531309)
            ·
              refine ⟨107127501505998450344824241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285673337349329200919531309 107127501505998450344824241)
              ·
                refine ⟨80345626129498837758618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107127501505998450344824241 80345626129498837758618181)
                ·
                  refine ⟨15064804899281032079740909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80345626129498837758618181 15064804899281032079740909)
                  ·
                    refine ⟨5649301837230387029902841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15064804899281032079740909 5649301837230387029902841)
                    ·
                      refine ⟨4236976377922790272427131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649301837230387029902841 4236976377922790272427131)
                      ·
                        rfl

theorem cell23_8251482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_8251482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251482 prefixEnd_8251482 := by exact prefixLift 8251482
  have htrace : WordTrace (prefixWord ++ tailWord_8251482) baseStart_8251482 baseEnd_8251482 := by
    simpa [prefixWord, tailWord_8251482, baseEnd_8251482] using wordTrace_append hprefix tailTrace_8251482
  have hstable : (prefixWord ++ tailWord_8251482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251482).length < 2 ^ (prefixWord ++ tailWord_8251482).sum := by decide
  have hdescent : baseEnd_8251482 < baseStart_8251482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251492 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_8251492 : Nat := 118140960795 + 8251492 * 2 ^ 59
def prefixEnd_8251492 : Nat := 4983230072969 + 3 ^ 40 * 8251492 * 2
def baseEnd_8251492 : Nat := 1412327170909778411100695

theorem tailTrace_8251492 : CollatzResearch.WordTrace tailWord_8251492 prefixEnd_8251492 1412327170909778411100695 := by
  unfold tailWord_8251492
  simp only [CollatzResearch.WordTrace]
  refine ⟨150478318911130600741586365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200637758548174134322115153 150478318911130600741586365)
  ·
    refine ⟨56429369591673975278094887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150478318911130600741586365 56429369591673975278094887)
    ·
      refine ⟨84644054387510962917142331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56429369591673975278094887 84644054387510962917142331)
      ·
        refine ⟨126966081581266444375713497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84644054387510962917142331 126966081581266444375713497)
        ·
          refine ⟨95224561185949833281785123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126966081581266444375713497 95224561185949833281785123)
          ·
            refine ⟨142836841778924749922677685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95224561185949833281785123 142836841778924749922677685)
            ·
              refine ⟨13390953916774195305251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142836841778924749922677685 13390953916774195305251033)
              ·
                refine ⟨10043215437580646478938275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13390953916774195305251033 10043215437580646478938275)
                ·
                  refine ⟨15064823156370969718407413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043215437580646478938275 15064823156370969718407413)
                  ·
                    refine ⟨1412327170909778411100695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15064823156370969718407413 1412327170909778411100695)
                    ·
                      rfl

theorem cell23_8251492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_8251492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251492 prefixEnd_8251492 := by exact prefixLift 8251492
  have htrace : WordTrace (prefixWord ++ tailWord_8251492) baseStart_8251492 baseEnd_8251492 := by
    simpa [prefixWord, tailWord_8251492, baseEnd_8251492] using wordTrace_append hprefix tailTrace_8251492
  have hstable : (prefixWord ++ tailWord_8251492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251492).length < 2 ^ (prefixWord ++ tailWord_8251492).sum := by decide
  have hdescent : baseEnd_8251492 < baseStart_8251492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251505 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_8251505 : Nat := 118140960795 + 8251505 * 2 ^ 59
def prefixEnd_8251505 : Nat := 4983230072969 + 3 ^ 40 * 8251505 * 2
def baseEnd_8251505 : Nat := 1412329395992614560813175

theorem tailTrace_8251505 : CollatzResearch.WordTrace tailWord_8251505 prefixEnd_8251505 1412329395992614560813175 := by
  unfold tailWord_8251505
  simp only [CollatzResearch.WordTrace]
  refine ⟨300957111971214104703395969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200638074647476069802263979 300957111971214104703395969)
  ·
    refine ⟨225717833978410578527546977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300957111971214104703395969 225717833978410578527546977)
    ·
      refine ⟨169288375483807933895660233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225717833978410578527546977 169288375483807933895660233)
      ·
        refine ⟨126966281612855950421745175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169288375483807933895660233 126966281612855950421745175)
        ·
          refine ⟨190449422419283925632617763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126966281612855950421745175 190449422419283925632617763)
          ·
            refine ⟨285674133628925888448926645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190449422419283925632617763 285674133628925888448926645)
            ·
              refine ⟨26781950027711802042086873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285674133628925888448926645 26781950027711802042086873)
              ·
                refine ⟨20086462520783851531565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26781950027711802042086873 20086462520783851531565155)
                ·
                  refine ⟨30129693781175777297347733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20086462520783851531565155 30129693781175777297347733)
                  ·
                    refine ⟨1412329395992614560813175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30129693781175777297347733 1412329395992614560813175)
                    ·
                      rfl

theorem cell23_8251505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_8251505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251505 prefixEnd_8251505 := by exact prefixLift 8251505
  have htrace : WordTrace (prefixWord ++ tailWord_8251505) baseStart_8251505 baseEnd_8251505 := by
    simpa [prefixWord, tailWord_8251505, baseEnd_8251505] using wordTrace_append hprefix tailTrace_8251505
  have hstable : (prefixWord ++ tailWord_8251505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251505).length < 2 ^ (prefixWord ++ tailWord_8251505).sum := by decide
  have hdescent : baseEnd_8251505 < baseStart_8251505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251523 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 1, 1, 3]
def baseStart_8251523 : Nat := 118140960795 + 8251523 * 2 ^ 59
def prefixEnd_8251523 : Nat := 4983230072969 + 3 ^ 40 * 8251523 * 2
def baseEnd_8251523 : Nat := 4236997430629624612014443

theorem tailTrace_8251523 : CollatzResearch.WordTrace tailWord_8251523 prefixEnd_8251523 4236997430629624612014443 := by
  unfold tailWord_8251523
  simp only [CollatzResearch.WordTrace]
  refine ⟨300957768485148893777551223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200638512323432595851700815 300957768485148893777551223)
  ·
    refine ⟨451436652727723340666326835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300957768485148893777551223 451436652727723340666326835)
    ·
      refine ⟨677154979091585010999490253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451436652727723340666326835 677154979091585010999490253)
      ·
        refine ⟨253933117159344379124808845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677154979091585010999490253 253933117159344379124808845)
        ·
          refine ⟨95224918934754142171803317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253933117159344379124808845 95224918934754142171803317)
          ·
            refine ⟨8927336150133200828606561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95224918934754142171803317 8927336150133200828606561)
            ·
              refine ⟨6695502112599900621454921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8927336150133200828606561 6695502112599900621454921)
              ·
                refine ⟨5021626584449925466091191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6695502112599900621454921 5021626584449925466091191)
                ·
                  refine ⟨7532439876674888199136787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021626584449925466091191 7532439876674888199136787)
                  ·
                    refine ⟨11298659815012332298705181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7532439876674888199136787 11298659815012332298705181)
                    ·
                      refine ⟨4236997430629624612014443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11298659815012332298705181 4236997430629624612014443)
                      ·
                        rfl

theorem cell23_8251523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_8251523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251523 prefixEnd_8251523 := by exact prefixLift 8251523
  have htrace : WordTrace (prefixWord ++ tailWord_8251523) baseStart_8251523 baseEnd_8251523 := by
    simpa [prefixWord, tailWord_8251523, baseEnd_8251523] using wordTrace_append hprefix tailTrace_8251523
  have hstable : (prefixWord ++ tailWord_8251523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251523).length < 2 ^ (prefixWord ++ tailWord_8251523).sum := by decide
  have hdescent : baseEnd_8251523 < baseStart_8251523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251529 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 3, 2, 2]
def baseStart_8251529 : Nat := 118140960795 + 8251529 * 2 ^ 59
def prefixEnd_8251529 : Nat := 4983230072969 + 3 ^ 40 * 8251529 * 2
def baseEnd_8251529 : Nat := 4237000511513551588539415

theorem tailTrace_8251529 : CollatzResearch.WordTrace tailWord_8251529 prefixEnd_8251529 4237000511513551588539415 := by
  unfold tailWord_8251529
  simp only [CollatzResearch.WordTrace]
  refine ⟨300957987323127156802269641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200638658215418104534846427 300957987323127156802269641)
  ·
    refine ⟨225718490492345367601702231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300957987323127156802269641 225718490492345367601702231)
    ·
      refine ⟨338577735738518051402553347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225718490492345367601702231 338577735738518051402553347)
      ·
        refine ⟨507866603607777077103830021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338577735738518051402553347 507866603607777077103830021)
        ·
          refine ⟨95224988176458201956968129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507866603607777077103830021 95224988176458201956968129)
          ·
            refine ⟨71418741132343651467726097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95224988176458201956968129 71418741132343651467726097)
            ·
              refine ⟨53564055849257738600794573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71418741132343651467726097 53564055849257738600794573)
              ·
                refine ⟨20086520943471651975297965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53564055849257738600794573 20086520943471651975297965)
                ·
                  refine ⟨7532445353801869490736737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20086520943471651975297965 7532445353801869490736737)
                  ·
                    refine ⟨5649334015351402118052553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532445353801869490736737 5649334015351402118052553)
                    ·
                      refine ⟨4237000511513551588539415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649334015351402118052553 4237000511513551588539415)
                      ·
                        rfl

theorem cell23_8251529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2, 2].length) (baseStart_8251529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251529 prefixEnd_8251529 := by exact prefixLift 8251529
  have htrace : WordTrace (prefixWord ++ tailWord_8251529) baseStart_8251529 baseEnd_8251529 := by
    simpa [prefixWord, tailWord_8251529, baseEnd_8251529] using wordTrace_append hprefix tailTrace_8251529
  have hstable : (prefixWord ++ tailWord_8251529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251529).length < 2 ^ (prefixWord ++ tailWord_8251529).sum := by decide
  have hdescent : baseEnd_8251529 < baseStart_8251529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251550 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_8251550 : Nat := 118140960795 + 8251550 * 2 ^ 59
def prefixEnd_8251550 : Nat := 4983230072969 + 3 ^ 40 * 8251550 * 2
def baseEnd_8251550 : Nat := 4237011294607296006376819

theorem tailTrace_8251550 : CollatzResearch.WordTrace tailWord_8251550 prefixEnd_8251550 4237011294607296006376819 := by
  unfold tailWord_8251550
  simp only [CollatzResearch.WordTrace]
  refine ⟨37619844157006384673598013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200639168837367384925856069 37619844157006384673598013)
  ·
    refine ⟨14107441558877394252599255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37619844157006384673598013 14107441558877394252599255)
    ·
      refine ⟨21161162338316091378898883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107441558877394252599255 21161162338316091378898883)
      ·
        refine ⟨31741743507474137068348325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21161162338316091378898883 31741743507474137068348325)
        ·
          refine ⟨5951576907651400700315311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31741743507474137068348325 5951576907651400700315311)
          ·
            refine ⟨8927365361477101050472967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951576907651400700315311 8927365361477101050472967)
            ·
              refine ⟨13391048042215651575709451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927365361477101050472967 13391048042215651575709451)
              ·
                refine ⟨20086572063323477363564177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13391048042215651575709451 20086572063323477363564177)
                ·
                  refine ⟨15064929047492608022673133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20086572063323477363564177 15064929047492608022673133)
                  ·
                    refine ⟨5649348392809728008502425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15064929047492608022673133 5649348392809728008502425)
                    ·
                      refine ⟨4237011294607296006376819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649348392809728008502425 4237011294607296006376819)
                      ·
                        rfl

theorem cell23_8251550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_8251550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251550 prefixEnd_8251550 := by exact prefixLift 8251550
  have htrace : WordTrace (prefixWord ++ tailWord_8251550) baseStart_8251550 baseEnd_8251550 := by
    simpa [prefixWord, tailWord_8251550, baseEnd_8251550] using wordTrace_append hprefix tailTrace_8251550
  have hstable : (prefixWord ++ tailWord_8251550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251550).length < 2 ^ (prefixWord ++ tailWord_8251550).sum := by decide
  have hdescent : baseEnd_8251550 < baseStart_8251550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251552 : List Nat := [2, 1, 1, 4, 2, 3, 3, 7]
def baseStart_8251552 : Nat := 118140960795 + 8251552 * 2 ^ 59
def prefixEnd_8251552 : Nat := 4983230072969 + 3 ^ 40 * 8251552 * 2
def baseEnd_8251552 : Nat := 156926382280318703650067

theorem tailTrace_8251552 : CollatzResearch.WordTrace tailWord_8251552 prefixEnd_8251552 156926382280318703650067 := by
  unfold tailWord_8251552
  simp only [CollatzResearch.WordTrace]
  refine ⟨150479413101021915865178455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200639217468029221153571273 150479413101021915865178455)
  ·
    refine ⟨225719119651532873797767683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150479413101021915865178455 225719119651532873797767683)
    ·
      refine ⟨338578679477299310696651525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225719119651532873797767683 338578679477299310696651525)
      ·
        refine ⟨63483502401993620755622161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338578679477299310696651525 63483502401993620755622161)
        ·
          refine ⟨47612626801495215566716621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63483502401993620755622161 47612626801495215566716621)
          ·
            refine ⟨17854735050560705837518733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47612626801495215566716621 17854735050560705837518733)
            ·
              refine ⟨6695525643960264689069525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17854735050560705837518733 6695525643960264689069525)
              ·
                refine ⟨156926382280318703650067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6695525643960264689069525 156926382280318703650067)
                ·
                  rfl

theorem cell23_8251552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 7].length) (baseStart_8251552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251552 prefixEnd_8251552 := by exact prefixLift 8251552
  have htrace : WordTrace (prefixWord ++ tailWord_8251552) baseStart_8251552 baseEnd_8251552 := by
    simpa [prefixWord, tailWord_8251552, baseEnd_8251552] using wordTrace_append hprefix tailTrace_8251552
  have hstable : (prefixWord ++ tailWord_8251552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251552).length < 2 ^ (prefixWord ++ tailWord_8251552).sum := by decide
  have hdescent : baseEnd_8251552 < baseStart_8251552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251573 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_8251573 : Nat := 118140960795 + 8251573 * 2 ^ 59
def prefixEnd_8251573 : Nat := 4983230072969 + 3 ^ 40 * 8251573 * 2
def baseEnd_8251573 : Nat := 1412341034887449805463071

theorem tailTrace_8251573 : CollatzResearch.WordTrace tailWord_8251573 prefixEnd_8251573 1412341034887449805463071 := by
  unfold tailWord_8251573
  simp only [CollatzResearch.WordTrace]
  refine ⟨300959592134967752316871373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200639728089978501544580915 300959592134967752316871373)
  ·
    refine ⟨112859847050612907118826765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300959592134967752316871373 112859847050612907118826765)
    ·
      refine ⟨42322442643979840169560037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112859847050612907118826765 42322442643979840169560037)
      ·
        refine ⟨7935457995746220031792507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42322442643979840169560037 7935457995746220031792507)
        ·
          refine ⟨11903186993619330047688761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935457995746220031792507 11903186993619330047688761)
          ·
            refine ⟨8927390245214497535766571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11903186993619330047688761 8927390245214497535766571)
            ·
              refine ⟨13391085367821746303649857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927390245214497535766571 13391085367821746303649857)
              ·
                refine ⟨10043314025866309727737393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13391085367821746303649857 10043314025866309727737393)
                ·
                  refine ⟨7532485519399732295803045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043314025866309727737393 7532485519399732295803045)
                  ·
                    refine ⟨1412341034887449805463071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532485519399732295803045 1412341034887449805463071)
                    ·
                      rfl

theorem cell23_8251573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_8251573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251573 prefixEnd_8251573 := by exact prefixLift 8251573
  have htrace : WordTrace (prefixWord ++ tailWord_8251573) baseStart_8251573 baseEnd_8251573 := by
    simpa [prefixWord, tailWord_8251573, baseEnd_8251573] using wordTrace_append hprefix tailTrace_8251573
  have hstable : (prefixWord ++ tailWord_8251573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251573).length < 2 ^ (prefixWord ++ tailWord_8251573).sum := by decide
  have hdescent : baseEnd_8251573 < baseStart_8251573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251595 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 6]
def baseStart_8251595 : Nat := 118140960795 + 8251595 * 2 ^ 59
def prefixEnd_8251595 : Nat := 4983230072969 + 3 ^ 40 * 8251595 * 2
def baseEnd_8251595 : Nat := 1412344800412249443438037

theorem tailTrace_8251595 : CollatzResearch.WordTrace tailWord_8251595 prefixEnd_8251595 1412344800412249443438037 := by
  unfold tailWord_8251595
  simp only [CollatzResearch.WordTrace]
  refine ⟨300960394540888050074172239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200640263027258700049448159 300960394540888050074172239)
  ·
    refine ⟨451440591811332075111258359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300960394540888050074172239 451440591811332075111258359)
    ·
      refine ⟨677160887716998112666887539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451440591811332075111258359 677160887716998112666887539)
      ·
        refine ⟨1015741331575497169000331309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677160887716998112666887539 1015741331575497169000331309)
        ·
          refine ⟨380902999340811438375124241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1015741331575497169000331309 380902999340811438375124241)
          ·
            refine ⟨285677249505608578781343181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380902999340811438375124241 285677249505608578781343181)
            ·
              refine ⟨107128968564603217043003693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285677249505608578781343181 107128968564603217043003693)
              ·
                refine ⟨40173363211726206391126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107128968564603217043003693 40173363211726206391126385)
                ·
                  refine ⟨30130022408794654793344789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40173363211726206391126385 30130022408794654793344789)
                  ·
                    refine ⟨1412344800412249443438037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30130022408794654793344789 1412344800412249443438037)
                    ·
                      rfl

theorem cell23_8251595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_8251595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251595 prefixEnd_8251595 := by exact prefixLift 8251595
  have htrace : WordTrace (prefixWord ++ tailWord_8251595) baseStart_8251595 baseEnd_8251595 := by
    simpa [prefixWord, tailWord_8251595, baseEnd_8251595] using wordTrace_append hprefix tailTrace_8251595
  have hstable : (prefixWord ++ tailWord_8251595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251595).length < 2 ^ (prefixWord ++ tailWord_8251595).sum := by decide
  have hdescent : baseEnd_8251595 < baseStart_8251595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251635 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_8251635 : Nat := 118140960795 + 8251635 * 2 ^ 59
def prefixEnd_8251635 : Nat := 4983230072969 + 3 ^ 40 * 8251635 * 2
def baseEnd_8251635 : Nat := 4237054940462928173813927

theorem tailTrace_8251635 : CollatzResearch.WordTrace tailWord_8251635 prefixEnd_8251635 4237054940462928173813927 := by
  unfold tailWord_8251635
  simp only [CollatzResearch.WordTrace]
  refine ⟨300961853460743136905628359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200641235640495424603752239 300961853460743136905628359)
  ·
    refine ⟨451442780191114705358442539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300961853460743136905628359 451442780191114705358442539)
    ·
      refine ⟨677164170286672058037663809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451442780191114705358442539 677164170286672058037663809)
      ·
        refine ⟨507873127715004043528247857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677164170286672058037663809 507873127715004043528247857)
        ·
          refine ⟨380904845786253032646185893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507873127715004043528247857 380904845786253032646185893)
          ·
            refine ⟨71419658584922443621159855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380904845786253032646185893 71419658584922443621159855)
            ·
              refine ⟨107129487877383665431739783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71419658584922443621159855 107129487877383665431739783)
              ·
                refine ⟨160694231816075498147609675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107129487877383665431739783 160694231816075498147609675)
                ·
                  refine ⟨241041347724113247221414513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160694231816075498147609675 241041347724113247221414513)
                  ·
                    refine ⟨180781010793084935416060885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241041347724113247221414513 180781010793084935416060885)
                    ·
                      refine ⟨4237054940462928173813927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180781010793084935416060885 4237054940462928173813927)
                      ·
                        rfl

theorem cell23_8251635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_8251635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251635 prefixEnd_8251635 := by exact prefixLift 8251635
  have htrace : WordTrace (prefixWord ++ tailWord_8251635) baseStart_8251635 baseEnd_8251635 := by
    simpa [prefixWord, tailWord_8251635, baseEnd_8251635] using wordTrace_append hprefix tailTrace_8251635
  have hstable : (prefixWord ++ tailWord_8251635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251635).length < 2 ^ (prefixWord ++ tailWord_8251635).sum := by decide
  have hdescent : baseEnd_8251635 < baseStart_8251635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251642 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_8251642 : Nat := 118140960795 + 8251642 * 2 ^ 59
def prefixEnd_8251642 : Nat := 4983230072969 + 3 ^ 40 * 8251642 * 2
def baseEnd_8251642 : Nat := 470784281647501071825155

theorem tailTrace_8251642 : CollatzResearch.WordTrace tailWord_8251642 prefixEnd_8251642 470784281647501071825155 := by
  unfold tailWord_8251642
  simp only [CollatzResearch.WordTrace]
  refine ⟨75240527192929444275283295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200641405847811851400755453 75240527192929444275283295)
  ·
    refine ⟨112860790789394166412924943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75240527192929444275283295 112860790789394166412924943)
    ·
      refine ⟨169291186184091249619387415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112860790789394166412924943 169291186184091249619387415)
      ·
        refine ⟨253936779276136874429081123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169291186184091249619387415 253936779276136874429081123)
        ·
          refine ⟨380905168914205311643621685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253936779276136874429081123 380905168914205311643621685)
          ·
            refine ⟨35709859585706747966589533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380905168914205311643621685 35709859585706747966589533)
            ·
              refine ⟨13391197344640030487471075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35709859585706747966589533 13391197344640030487471075)
              ·
                refine ⟨20086796016960045731206613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13391197344640030487471075 20086796016960045731206613)
                ·
                  refine ⟨470784281647501071825155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20086796016960045731206613 470784281647501071825155)
                  ·
                    rfl

theorem cell23_8251642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_8251642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251642 prefixEnd_8251642 := by exact prefixLift 8251642
  have htrace : WordTrace (prefixWord ++ tailWord_8251642) baseStart_8251642 baseEnd_8251642 := by
    simpa [prefixWord, tailWord_8251642, baseEnd_8251642] using wordTrace_append hprefix tailTrace_8251642
  have hstable : (prefixWord ++ tailWord_8251642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251642).length < 2 ^ (prefixWord ++ tailWord_8251642).sum := by decide
  have hdescent : baseEnd_8251642 < baseStart_8251642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251693 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 5]
def baseStart_8251693 : Nat := 118140960795 + 8251693 * 2 ^ 59
def prefixEnd_8251693 : Nat := 4983230072969 + 3 ^ 40 * 8251693 * 2
def baseEnd_8251693 : Nat := 470787191371209882987629

theorem tailTrace_8251693 : CollatzResearch.WordTrace tailWord_8251693 prefixEnd_8251693 470787191371209882987629 := by
  unfold tailWord_8251693
  simp only [CollatzResearch.WordTrace]
  refine ⟨300963968894533012811239733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200642645929688675207493155 300963968894533012811239733)
  ·
    refine ⟨28215372083862469951053725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300963968894533012811239733 28215372083862469951053725)
    ·
      refine ⟨10580764531448426231645147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28215372083862469951053725 10580764531448426231645147)
      ·
        refine ⟨15871146797172639347467721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10580764531448426231645147 15871146797172639347467721)
        ·
          refine ⟨11903360097879479510600791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15871146797172639347467721 11903360097879479510600791)
          ·
            refine ⟨17855040146819219265901187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11903360097879479510600791 17855040146819219265901187)
            ·
              refine ⟨26782560220228828898851781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855040146819219265901187 26782560220228828898851781)
              ·
                refine ⟨5021730041292905418534709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26782560220228828898851781 5021730041292905418534709)
                ·
                  refine ⟨470787191371209882987629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021730041292905418534709 470787191371209882987629)
                  ·
                    rfl

theorem cell23_8251693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_8251693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251693 prefixEnd_8251693 := by exact prefixLift 8251693
  have htrace : WordTrace (prefixWord ++ tailWord_8251693) baseStart_8251693 baseEnd_8251693 := by
    simpa [prefixWord, tailWord_8251693, baseEnd_8251693] using wordTrace_append hprefix tailTrace_8251693
  have hstable : (prefixWord ++ tailWord_8251693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251693).length < 2 ^ (prefixWord ++ tailWord_8251693).sum := by decide
  have hdescent : baseEnd_8251693 < baseStart_8251693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251719 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 3, 4]
def baseStart_8251719 : Nat := 118140960795 + 8251719 * 2 ^ 59
def prefixEnd_8251719 : Nat := 4983230072969 + 3 ^ 40 * 8251719 * 2
def baseEnd_8251719 : Nat := 1412366024279301948387847

theorem tailTrace_8251719 : CollatzResearch.WordTrace tailWord_8251719 prefixEnd_8251719 1412366024279301948387847 := by
  unfold tailWord_8251719
  simp only [CollatzResearch.WordTrace]
  refine ⟨300964917192438819251686211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200643278128292546167790807 300964917192438819251686211)
  ·
    refine ⟨451447375788658228877529317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300964917192438819251686211 451447375788658228877529317)
    ·
      refine ⟨84646382960373417914536747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451447375788658228877529317 84646382960373417914536747)
      ·
        refine ⟨126969574440560126871805121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84646382960373417914536747 126969574440560126871805121)
        ·
          refine ⟨95227180830420095153853841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126969574440560126871805121 95227180830420095153853841)
          ·
            refine ⟨71420385622815071365390381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95227180830420095153853841 71420385622815071365390381)
            ·
              refine ⟨26782644608555651762021393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71420385622815071365390381 26782644608555651762021393)
              ·
                refine ⟨20086983456416738821516045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26782644608555651762021393 20086983456416738821516045)
                ·
                  refine ⟨7532618796156277058068517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20086983456416738821516045 7532618796156277058068517)
                  ·
                    refine ⟨1412366024279301948387847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532618796156277058068517 1412366024279301948387847)
                    ·
                      rfl

theorem cell23_8251719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_8251719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251719 prefixEnd_8251719 := by exact prefixLift 8251719
  have htrace : WordTrace (prefixWord ++ tailWord_8251719) baseStart_8251719 baseEnd_8251719 := by
    simpa [prefixWord, tailWord_8251719, baseEnd_8251719] using wordTrace_append hprefix tailTrace_8251719
  have hstable : (prefixWord ++ tailWord_8251719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251719).length < 2 ^ (prefixWord ++ tailWord_8251719).sum := by decide
  have hdescent : baseEnd_8251719 < baseStart_8251719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251729 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_8251729 : Nat := 118140960795 + 8251729 * 2 ^ 59
def prefixEnd_8251729 : Nat := 4983230072969 + 3 ^ 40 * 8251729 * 2
def baseEnd_8251729 : Nat := 4237103207644450806038495

theorem tailTrace_8251729 : CollatzResearch.WordTrace tailWord_8251729 prefixEnd_8251729 4237103207644450806038495 := by
  unfold tailWord_8251729
  simp only [CollatzResearch.WordTrace]
  refine ⟨300965281922402590959550241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200643521281601727306366827 300965281922402590959550241)
  ·
    refine ⟨225723961441801943219662681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300965281922402590959550241 225723961441801943219662681)
    ·
      refine ⟨169292971081351457414747011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225723961441801943219662681 169292971081351457414747011)
      ·
        refine ⟨253939456622027186122120517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169292971081351457414747011 253939456622027186122120517)
        ·
          refine ⟨47613648116630097397897597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253939456622027186122120517 47613648116630097397897597)
          ·
            refine ⟨17855118043736286524211599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47613648116630097397897597 17855118043736286524211599)
            ·
              refine ⟨26782677065604429786317399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855118043736286524211599 26782677065604429786317399)
              ·
                refine ⟨40174015598406644679476099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26782677065604429786317399 40174015598406644679476099)
                ·
                  refine ⟨60261023397609967019214149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40174015598406644679476099 60261023397609967019214149)
                  ·
                    refine ⟨11298941887051868816102653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60261023397609967019214149 11298941887051868816102653)
                    ·
                      refine ⟨4237103207644450806038495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11298941887051868816102653 4237103207644450806038495)
                      ·
                        rfl

theorem cell23_8251729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_8251729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251729 prefixEnd_8251729 := by exact prefixLift 8251729
  have htrace : WordTrace (prefixWord ++ tailWord_8251729) baseStart_8251729 baseEnd_8251729 := by
    simpa [prefixWord, tailWord_8251729, baseEnd_8251729] using wordTrace_append hprefix tailTrace_8251729
  have hstable : (prefixWord ++ tailWord_8251729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251729).length < 2 ^ (prefixWord ++ tailWord_8251729).sum := by decide
  have hdescent : baseEnd_8251729 < baseStart_8251729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251749 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 6]
def baseStart_8251749 : Nat := 118140960795 + 8251749 * 2 ^ 59
def prefixEnd_8251749 : Nat := 4983230072969 + 3 ^ 40 * 8251749 * 2
def baseEnd_8251749 : Nat := 470790386361948969754267

theorem tailTrace_8251749 : CollatzResearch.WordTrace tailWord_8251749 prefixEnd_8251749 470790386361948969754267 := by
  unfold tailWord_8251749
  simp only [CollatzResearch.WordTrace]
  refine ⟨300966011382330134375278301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200644007588220089583518867 300966011382330134375278301)
  ·
    refine ⟨112862254268373800390729363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300966011382330134375278301 112862254268373800390729363)
    ·
      refine ⟨169293381402560700586094045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112862254268373800390729363 169293381402560700586094045)
      ·
        refine ⟨63485018025960262719785267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169293381402560700586094045 63485018025960262719785267)
        ·
          refine ⟨95227527038940394079677901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63485018025960262719785267 95227527038940394079677901)
          ·
            refine ⟨35710322639602647779879213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95227527038940394079677901 35710322639602647779879213)
            ·
              refine ⟨13391370989850992917454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35710322639602647779879213 13391370989850992917454705)
              ·
                refine ⟨10043528242388244688091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13391370989850992917454705 10043528242388244688091029)
                ·
                  refine ⟨470790386361948969754267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10043528242388244688091029 470790386361948969754267)
                  ·
                    rfl

theorem cell23_8251749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_8251749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251749 prefixEnd_8251749 := by exact prefixLift 8251749
  have htrace : WordTrace (prefixWord ++ tailWord_8251749) baseStart_8251749 baseEnd_8251749 := by
    simpa [prefixWord, tailWord_8251749, baseEnd_8251749] using wordTrace_append hprefix tailTrace_8251749
  have hstable : (prefixWord ++ tailWord_8251749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251749).length < 2 ^ (prefixWord ++ tailWord_8251749).sum := by decide
  have hdescent : baseEnd_8251749 < baseStart_8251749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251826 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_8251826 : Nat := 118140960795 + 8251826 * 2 ^ 59
def prefixEnd_8251826 : Nat := 4983230072969 + 3 ^ 40 * 8251826 * 2
def baseEnd_8251826 : Nat := 1412384338422645642175183

theorem tailTrace_8251826 : CollatzResearch.WordTrace tailWord_8251826 prefixEnd_8251826 1412384338422645642175183 := by
  unfold tailWord_8251826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75242204950762794131457833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200645879868700784350554221 75242204950762794131457833)
  ·
    refine ⟨56431653713072095598593375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75242204950762794131457833 56431653713072095598593375)
    ·
      refine ⟨84647480569608143397890063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56431653713072095598593375 84647480569608143397890063)
      ·
        refine ⟨126971220854412215096835095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84647480569608143397890063 126971220854412215096835095)
        ·
          refine ⟨190456831281618322645252643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126971220854412215096835095 190456831281618322645252643)
          ·
            refine ⟨285685246922427483967878965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190456831281618322645252643 285685246922427483967878965)
            ·
              refine ⟨26782991898977576621988653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285685246922427483967878965 26782991898977576621988653)
              ·
                refine ⟨10043621962116591233245745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26782991898977576621988653 10043621962116591233245745)
                ·
                  refine ⟨7532716471587443424934309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043621962116591233245745 7532716471587443424934309)
                  ·
                    refine ⟨1412384338422645642175183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532716471587443424934309 1412384338422645642175183)
                    ·
                      rfl

theorem cell23_8251826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_8251826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251826 prefixEnd_8251826 := by exact prefixLift 8251826
  have htrace : WordTrace (prefixWord ++ tailWord_8251826) baseStart_8251826 baseEnd_8251826 := by
    simpa [prefixWord, tailWord_8251826, baseEnd_8251826] using wordTrace_append hprefix tailTrace_8251826
  have hstable : (prefixWord ++ tailWord_8251826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251826).length < 2 ^ (prefixWord ++ tailWord_8251826).sum := by decide
  have hdescent : baseEnd_8251826 < baseStart_8251826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251833 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_8251833 : Nat := 118140960795 + 8251833 * 2 ^ 59
def prefixEnd_8251833 : Nat := 4983230072969 + 3 ^ 40 * 8251833 * 2
def baseEnd_8251833 : Nat := 4237156609632518399138017

theorem tailTrace_8251833 : CollatzResearch.WordTrace tailWord_8251833 prefixEnd_8251833 4237156609632518399138017 := by
  unfold tailWord_8251833
  simp only [CollatzResearch.WordTrace]
  refine ⟨300969075114025816721336153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200646050076017211147557435 300969075114025816721336153)
  ·
    refine ⟨225726806335519362541002115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300969075114025816721336153 225726806335519362541002115)
    ·
      refine ⟨338590209503279043811503173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225726806335519362541002115 338590209503279043811503173)
      ·
        refine ⟨63485664281864820714656845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338590209503279043811503173 63485664281864820714656845)
        ·
          refine ⟨23807124105699307767996317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63485664281864820714656845 23807124105699307767996317)
          ·
            refine ⟨8927671539637240412998619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23807124105699307767996317 8927671539637240412998619)
            ·
              refine ⟨13391507309455860619497929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927671539637240412998619 13391507309455860619497929)
              ·
                refine ⟨10043630482091895464623447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13391507309455860619497929 10043630482091895464623447)
                ·
                  refine ⟨15065445723137843196935171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043630482091895464623447 15065445723137843196935171)
                  ·
                    refine ⟨22598168584706764795402757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15065445723137843196935171 22598168584706764795402757)
                    ·
                      refine ⟨4237156609632518399138017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22598168584706764795402757 4237156609632518399138017)
                      ·
                        rfl

theorem cell23_8251833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_8251833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251833 prefixEnd_8251833 := by exact prefixLift 8251833
  have htrace : WordTrace (prefixWord ++ tailWord_8251833) baseStart_8251833 baseEnd_8251833 := by
    simpa [prefixWord, tailWord_8251833, baseEnd_8251833] using wordTrace_append hprefix tailTrace_8251833
  have hstable : (prefixWord ++ tailWord_8251833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251833).length < 2 ^ (prefixWord ++ tailWord_8251833).sum := by decide
  have hdescent : baseEnd_8251833 < baseStart_8251833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251849 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_8251849 : Nat := 118140960795 + 8251849 * 2 ^ 59
def prefixEnd_8251849 : Nat := 4983230072969 + 3 ^ 40 * 8251849 * 2
def baseEnd_8251849 : Nat := 4237164825322990336537943

theorem tailTrace_8251849 : CollatzResearch.WordTrace tailWord_8251849 prefixEnd_8251849 4237164825322990336537943 := by
  unfold tailWord_8251849
  simp only [CollatzResearch.WordTrace]
  refine ⟨300969658681967851453918601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200646439121311900969279067 300969658681967851453918601)
  ·
    refine ⟨225727244011475888590438951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300969658681967851453918601 225727244011475888590438951)
    ·
      refine ⟨338590866017213832885658427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225727244011475888590438951 338590866017213832885658427)
      ·
        refine ⟨507886299025820749328487641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338590866017213832885658427 507886299025820749328487641)
        ·
          refine ⟨380914724269365561996365731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507886299025820749328487641 380914724269365561996365731)
          ·
            refine ⟨571372086404048342994548597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380914724269365561996365731 571372086404048342994548597)
            ·
              refine ⟨53566133100379532155738931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 571372086404048342994548597 53566133100379532155738931)
              ·
                refine ⟨80349199650569298233608397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53566133100379532155738931 80349199650569298233608397)
                ·
                  refine ⟨30130949868963486837603149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80349199650569298233608397 30130949868963486837603149)
                  ·
                    refine ⟨11299106200861307564101181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30130949868963486837603149 11299106200861307564101181)
                    ·
                      refine ⟨4237164825322990336537943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299106200861307564101181 4237164825322990336537943)
                      ·
                        rfl

theorem cell23_8251849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_8251849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251849 prefixEnd_8251849 := by exact prefixLift 8251849
  have htrace : WordTrace (prefixWord ++ tailWord_8251849) baseStart_8251849 baseEnd_8251849 := by
    simpa [prefixWord, tailWord_8251849, baseEnd_8251849] using wordTrace_append hprefix tailTrace_8251849
  have hstable : (prefixWord ++ tailWord_8251849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251849).length < 2 ^ (prefixWord ++ tailWord_8251849).sum := by decide
  have hdescent : baseEnd_8251849 < baseStart_8251849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251850 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_8251850 : Nat := 118140960795 + 8251850 * 2 ^ 59
def prefixEnd_8251850 : Nat := 4983230072969 + 3 ^ 40 * 8251850 * 2
def baseEnd_8251850 : Nat := 4237165338803644832625439

theorem tailTrace_8251850 : CollatzResearch.WordTrace tailWord_8251850 prefixEnd_8251850 4237165338803644832625439 := by
  unfold tailWord_8251850
  simp only [CollatzResearch.WordTrace]
  refine ⟨75242423788741057156176251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200646463436642819083136669 75242423788741057156176251)
  ·
    refine ⟨112863635683111585734264377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75242423788741057156176251 112863635683111585734264377)
    ·
      refine ⟨84647726762333689300698283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112863635683111585734264377 84647726762333689300698283)
      ·
        refine ⟨126971590143500533951047425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84647726762333689300698283 126971590143500533951047425)
        ·
          refine ⟨95228692607625400463285569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126971590143500533951047425 95228692607625400463285569)
          ·
            refine ⟨71421519455719050347464177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95228692607625400463285569 71421519455719050347464177)
            ·
              refine ⟨53566139591789287760598133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71421519455719050347464177 53566139591789287760598133)
              ·
                refine ⟨5021825586730245727556075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53566139591789287760598133 5021825586730245727556075)
                ·
                  refine ⟨7532738380095368591334113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021825586730245727556075 7532738380095368591334113)
                  ·
                    refine ⟨5649553785071526443500585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532738380095368591334113 5649553785071526443500585)
                    ·
                      refine ⟨4237165338803644832625439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649553785071526443500585 4237165338803644832625439)
                      ·
                        rfl

theorem cell23_8251850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_8251850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251850 prefixEnd_8251850 := by exact prefixLift 8251850
  have htrace : WordTrace (prefixWord ++ tailWord_8251850) baseStart_8251850 baseEnd_8251850 := by
    simpa [prefixWord, tailWord_8251850, baseEnd_8251850] using wordTrace_append hprefix tailTrace_8251850
  have hstable : (prefixWord ++ tailWord_8251850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251850).length < 2 ^ (prefixWord ++ tailWord_8251850).sum := by decide
  have hdescent : baseEnd_8251850 < baseStart_8251850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251869 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_8251869 : Nat := 118140960795 + 8251869 * 2 ^ 59
def prefixEnd_8251869 : Nat := 4983230072969 + 3 ^ 40 * 8251869 * 2
def baseEnd_8251869 : Nat := 1412391698312026752762617

theorem tailTrace_8251869 : CollatzResearch.WordTrace tailWord_8251869 prefixEnd_8251869 1412391698312026752762617 := by
  unfold tailWord_8251869
  simp only [CollatzResearch.WordTrace]
  refine ⟨300970388141895394869646661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200646925427930263246431107 300970388141895394869646661)
  ·
    refine ⟨56431947776605386538058749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300970388141895394869646661 56431947776605386538058749)
    ·
      refine ⟨21161980416227019951772031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56431947776605386538058749 21161980416227019951772031)
      ·
        refine ⟨31742970624340529927658047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21161980416227019951772031 31742970624340529927658047)
        ·
          refine ⟨47614455936510794891487071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31742970624340529927658047 47614455936510794891487071)
          ·
            refine ⟨71421683904766192337230607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47614455936510794891487071 71421683904766192337230607)
            ·
              refine ⟨107132525857149288505845911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71421683904766192337230607 107132525857149288505845911)
              ·
                refine ⟨160698788785723932758768867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107132525857149288505845911 160698788785723932758768867)
                ·
                  refine ⟨241048183178585899138153301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160698788785723932758768867 241048183178585899138153301)
                  ·
                    refine ⟨1412391698312026752762617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241048183178585899138153301 1412391698312026752762617)
                    ·
                      rfl

theorem cell23_8251869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_8251869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251869 prefixEnd_8251869 := by exact prefixLift 8251869
  have htrace : WordTrace (prefixWord ++ tailWord_8251869) baseStart_8251869 baseEnd_8251869 := by
    simpa [prefixWord, tailWord_8251869, baseEnd_8251869] using wordTrace_append hprefix tailTrace_8251869
  have hstable : (prefixWord ++ tailWord_8251869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251869).length < 2 ^ (prefixWord ++ tailWord_8251869).sum := by decide
  have hdescent : baseEnd_8251869 < baseStart_8251869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251889 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_8251889 : Nat := 118140960795 + 8251889 * 2 ^ 59
def prefixEnd_8251889 : Nat := 4983230072969 + 3 ^ 40 * 8251889 * 2
def baseEnd_8251889 : Nat := 4237185364549170180037759

theorem tailTrace_8251889 : CollatzResearch.WordTrace tailWord_8251889 prefixEnd_8251889 4237185364549170180037759 := by
  unfold tailWord_8251889
  simp only [CollatzResearch.WordTrace]
  refine ⟨300971117601822938285374721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200647411734548625523583147 300971117601822938285374721)
  ·
    refine ⟨225728338201367203714031041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300971117601822938285374721 225728338201367203714031041)
    ·
      refine ⟨169296253651025402785523281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225728338201367203714031041 169296253651025402785523281)
      ·
        refine ⟨126972190238269052089142461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169296253651025402785523281 126972190238269052089142461)
        ·
          refine ⟨47614571339350894533428423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126972190238269052089142461 47614571339350894533428423)
          ·
            refine ⟨71421857009026341800142635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47614571339350894533428423 71421857009026341800142635)
            ·
              refine ⟨107132785513539512700213953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71421857009026341800142635 107132785513539512700213953)
              ·
                refine ⟨80349589135154634525160465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107132785513539512700213953 80349589135154634525160465)
                ·
                  refine ⟨60262191851365975893870349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80349589135154634525160465 60262191851365975893870349)
                  ·
                    refine ⟨22598321944262240960201381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60262191851365975893870349 22598321944262240960201381)
                    ·
                      refine ⟨4237185364549170180037759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22598321944262240960201381 4237185364549170180037759)
                      ·
                        rfl

theorem cell23_8251889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_8251889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251889 prefixEnd_8251889 := by exact prefixLift 8251889
  have htrace : WordTrace (prefixWord ++ tailWord_8251889) baseStart_8251889 baseEnd_8251889 := by
    simpa [prefixWord, tailWord_8251889, baseEnd_8251889] using wordTrace_append hprefix tailTrace_8251889
  have hstable : (prefixWord ++ tailWord_8251889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251889).length < 2 ^ (prefixWord ++ tailWord_8251889).sum := by decide
  have hdescent : baseEnd_8251889 < baseStart_8251889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251909 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_8251909 : Nat := 118140960795 + 8251909 * 2 ^ 59
def prefixEnd_8251909 : Nat := 4983230072969 + 3 ^ 40 * 8251909 * 2
def baseEnd_8251909 : Nat := 4237195634162260101787667

theorem tailTrace_8251909 : CollatzResearch.WordTrace tailWord_8251909 prefixEnd_8251909 4237195634162260101787667 := by
  unfold tailWord_8251909
  simp only [CollatzResearch.WordTrace]
  refine ⟨300971847061750481701102781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200647898041166987800735187 300971847061750481701102781)
  ·
    refine ⟨112864442648156430637913543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300971847061750481701102781 112864442648156430637913543)
    ·
      refine ⟨169296663972234645956870315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112864442648156430637913543 169296663972234645956870315)
      ·
        refine ⟨253944995958351968935305473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169296663972234645956870315 253944995958351968935305473)
        ·
          refine ⟨190458746968763976701479105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253944995958351968935305473 190458746968763976701479105)
          ·
            refine ⟨142844060226572982526109329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190458746968763976701479105 142844060226572982526109329)
            ·
              refine ⟨107133045169929736894581997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142844060226572982526109329 107133045169929736894581997)
              ·
                refine ⟨40174891938723651335468249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107133045169929736894581997 40174891938723651335468249)
                ·
                  refine ⟨30131168954042738501601187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40174891938723651335468249 30131168954042738501601187)
                  ·
                    refine ⟨45196753431064107752401781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30131168954042738501601187 45196753431064107752401781)
                    ·
                      refine ⟨4237195634162260101787667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45196753431064107752401781 4237195634162260101787667)
                      ·
                        rfl

theorem cell23_8251909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_8251909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251909 prefixEnd_8251909 := by exact prefixLift 8251909
  have htrace : WordTrace (prefixWord ++ tailWord_8251909) baseStart_8251909 baseEnd_8251909 := by
    simpa [prefixWord, tailWord_8251909, baseEnd_8251909] using wordTrace_append hprefix tailTrace_8251909
  have hstable : (prefixWord ++ tailWord_8251909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251909).length < 2 ^ (prefixWord ++ tailWord_8251909).sum := by decide
  have hdescent : baseEnd_8251909 < baseStart_8251909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251917 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8251917 : Nat := 118140960795 + 8251917 * 2 ^ 59
def prefixEnd_8251917 : Nat := 4983230072969 + 3 ^ 40 * 8251917 * 2
def baseEnd_8251917 : Nat := 4237199742007496070487631

theorem tailTrace_8251917 : CollatzResearch.WordTrace tailWord_8251917 prefixEnd_8251917 4237199742007496070487631 := by
  unfold tailWord_8251917
  simp only [CollatzResearch.WordTrace]
  refine ⟨300972138845721499067394005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200648092563814332711596003 300972138845721499067394005)
  ·
    refine ⟨7054034504196597634392047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 300972138845721499067394005 7054034504196597634392047)
    ·
      refine ⟨10581051756294896451588071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054034504196597634392047 10581051756294896451588071)
      ·
        refine ⟨15871577634442344677382107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581051756294896451588071 15871577634442344677382107)
        ·
          refine ⟨23807366451663517016073161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15871577634442344677382107 23807366451663517016073161)
          ·
            refine ⟨17855524838747637762054871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23807366451663517016073161 17855524838747637762054871)
            ·
              refine ⟨26783287258121456643082307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855524838747637762054871 26783287258121456643082307)
              ·
                refine ⟨40174930887182184964623461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26783287258121456643082307 40174930887182184964623461)
                ·
                  refine ⟨7532799541346659680866899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40174930887182184964623461 7532799541346659680866899)
                  ·
                    refine ⟨11299199312019989521300349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7532799541346659680866899 11299199312019989521300349)
                    ·
                      refine ⟨4237199742007496070487631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299199312019989521300349 4237199742007496070487631)
                      ·
                        rfl

theorem cell23_8251917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8251917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251917 prefixEnd_8251917 := by exact prefixLift 8251917
  have htrace : WordTrace (prefixWord ++ tailWord_8251917) baseStart_8251917 baseEnd_8251917 := by
    simpa [prefixWord, tailWord_8251917, baseEnd_8251917] using wordTrace_append hprefix tailTrace_8251917
  have hstable : (prefixWord ++ tailWord_8251917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251917).length < 2 ^ (prefixWord ++ tailWord_8251917).sum := by decide
  have hdescent : baseEnd_8251917 < baseStart_8251917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251919 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_8251919 : Nat := 118140960795 + 8251919 * 2 ^ 59
def prefixEnd_8251919 : Nat := 4983230072969 + 3 ^ 40 * 8251919 * 2
def baseEnd_8251919 : Nat := 4237200768968805062662621

theorem tailTrace_8251919 : CollatzResearch.WordTrace tailWord_8251919 prefixEnd_8251919 4237200768968805062662621 := by
  unfold tailWord_8251919
  simp only [CollatzResearch.WordTrace]
  refine ⟨300972211791714253408966811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200648141194476168939311207 300972211791714253408966811)
  ·
    refine ⟨451458317687571380113450217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300972211791714253408966811 451458317687571380113450217)
    ·
      refine ⟨338593738265678535085087663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451458317687571380113450217 338593738265678535085087663)
      ·
        refine ⟨507890607398517802627631495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338593738265678535085087663 507890607398517802627631495)
        ·
          refine ⟨761835911097776703941447243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507890607398517802627631495 761835911097776703941447243)
          ·
            refine ⟨1142753866646665055912170865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761835911097776703941447243 1142753866646665055912170865)
            ·
              refine ⟨857065399984998791934128149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142753866646665055912170865 857065399984998791934128149)
              ·
                refine ⟨40174940624296818371912257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 857065399984998791934128149 40174940624296818371912257)
                ·
                  refine ⟨30131205468222613778934193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40174940624296818371912257 30131205468222613778934193)
                  ·
                    refine ⟨22598404101166960334200645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30131205468222613778934193 22598404101166960334200645)
                    ·
                      refine ⟨4237200768968805062662621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22598404101166960334200645 4237200768968805062662621)
                      ·
                        rfl

theorem cell23_8251919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_8251919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251919 prefixEnd_8251919 := by exact prefixLift 8251919
  have htrace : WordTrace (prefixWord ++ tailWord_8251919) baseStart_8251919 baseEnd_8251919 := by
    simpa [prefixWord, tailWord_8251919, baseEnd_8251919] using wordTrace_append hprefix tailTrace_8251919
  have hstable : (prefixWord ++ tailWord_8251919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251919).length < 2 ^ (prefixWord ++ tailWord_8251919).sum := by decide
  have hdescent : baseEnd_8251919 < baseStart_8251919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251923 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 4, 2, 2]
def baseStart_8251923 : Nat := 118140960795 + 8251923 * 2 ^ 59
def prefixEnd_8251923 : Nat := 4983230072969 + 3 ^ 40 * 8251923 * 2
def baseEnd_8251923 : Nat := 4237202822891423047012603

theorem tailTrace_8251923 : CollatzResearch.WordTrace tailWord_8251923 prefixEnd_8251923 4237202822891423047012603 := by
  unfold tailWord_8251923
  simp only [CollatzResearch.WordTrace]
  refine ⟨300972357683699762092112423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200648238455799841394741615 300972357683699762092112423)
  ·
    refine ⟨451458536525549643138168635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300972357683699762092112423 451458536525549643138168635)
    ·
      refine ⟨677187804788324464707252953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451458536525549643138168635 677187804788324464707252953)
      ·
        refine ⟨507890853591243348530439715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677187804788324464707252953 507890853591243348530439715)
        ·
          refine ⟨761836280386865022795659573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507890853591243348530439715 761836280386865022795659573)
          ·
            refine ⟨71422151286268595887093085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 761836280386865022795659573 71422151286268595887093085)
            ·
              refine ⟨26783306732350723457659907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71422151286268595887093085 26783306732350723457659907)
              ·
                refine ⟨40174960098526085186489861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26783306732350723457659907 40174960098526085186489861)
                ·
                  refine ⟨7532805018473640972466849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40174960098526085186489861 7532805018473640972466849)
                  ·
                    refine ⟨5649603763855230729350137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7532805018473640972466849 5649603763855230729350137)
                    ·
                      refine ⟨4237202822891423047012603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649603763855230729350137 4237202822891423047012603)
                      ·
                        rfl

theorem cell23_8251923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2, 2].length) (baseStart_8251923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251923 prefixEnd_8251923 := by exact prefixLift 8251923
  have htrace : WordTrace (prefixWord ++ tailWord_8251923) baseStart_8251923 baseEnd_8251923 := by
    simpa [prefixWord, tailWord_8251923, baseEnd_8251923] using wordTrace_append hprefix tailTrace_8251923
  have hstable : (prefixWord ++ tailWord_8251923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251923).length < 2 ^ (prefixWord ++ tailWord_8251923).sum := by decide
  have hdescent : baseEnd_8251923 < baseStart_8251923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251946 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_8251946 : Nat := 118140960795 + 8251946 * 2 ^ 59
def prefixEnd_8251946 : Nat := 4983230072969 + 3 ^ 40 * 8251946 * 2
def baseEnd_8251946 : Nat := 470801625882941828558333

theorem tailTrace_8251946 : CollatzResearch.WordTrace tailWord_8251946 prefixEnd_8251946 470801625882941828558333 := by
  unfold tailWord_8251946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75243299140654109255049923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200648797708410958013466461 75243299140654109255049923)
  ·
    refine ⟨112864948710981163882574885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75243299140654109255049923 112864948710981163882574885)
    ·
      refine ⟨21162177883308968227982791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112864948710981163882574885 21162177883308968227982791)
      ·
        refine ⟨31743266824963452341974187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21162177883308968227982791 31743266824963452341974187)
        ·
          refine ⟨47614900237445178512961281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31743266824963452341974187 47614900237445178512961281)
          ·
            refine ⟨35711175178083883884720961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47614900237445178512961281 35711175178083883884720961)
            ·
              refine ⟨26783381383562912913540721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35711175178083883884720961 26783381383562912913540721)
              ·
                refine ⟨20087536037672184685155541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26783381383562912913540721 20087536037672184685155541)
                ·
                  refine ⟨470801625882941828558333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20087536037672184685155541 470801625882941828558333)
                  ·
                    rfl

theorem cell23_8251946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_8251946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251946 prefixEnd_8251946 := by exact prefixLift 8251946
  have htrace : WordTrace (prefixWord ++ tailWord_8251946) baseStart_8251946 baseEnd_8251946 := by
    simpa [prefixWord, tailWord_8251946, baseEnd_8251946] using wordTrace_append hprefix tailTrace_8251946
  have hstable : (prefixWord ++ tailWord_8251946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251946).length < 2 ^ (prefixWord ++ tailWord_8251946).sum := by decide
  have hdescent : baseEnd_8251946 < baseStart_8251946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251959 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 7]
def baseStart_8251959 : Nat := 118140960795 + 8251959 * 2 ^ 59
def prefixEnd_8251959 : Nat := 4983230072969 + 3 ^ 40 * 8251959 * 2
def baseEnd_8251959 : Nat := 1412407102731661635387479

theorem tailTrace_8251959 : CollatzResearch.WordTrace tailWord_8251959 prefixEnd_8251959 1412407102731661635387479 := by
  unfold tailWord_8251959
  simp only [CollatzResearch.WordTrace]
  refine ⟨300973670711569340240422931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200649113807712893493615287 300973670711569340240422931)
  ·
    refine ⟨451460506067354010360634397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300973670711569340240422931 451460506067354010360634397)
    ·
      refine ⟨169297689775257753885237899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451460506067354010360634397 169297689775257753885237899)
      ·
        refine ⟨253946534662886630827856849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169297689775257753885237899 253946534662886630827856849)
        ·
          refine ⟨190459900997164973120892637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253946534662886630827856849 190459900997164973120892637)
          ·
            refine ⟨71422462873936864920334739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190459900997164973120892637 71422462873936864920334739)
            ·
              refine ⟨107133694310905297380502109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71422462873936864920334739 107133694310905297380502109)
              ·
                refine ⟨40175135366589486517688291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107133694310905297380502109 40175135366589486517688291)
                ·
                  refine ⟨60262703049884229776532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40175135366589486517688291 60262703049884229776532437)
                  ·
                    refine ⟨1412407102731661635387479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60262703049884229776532437 1412407102731661635387479)
                    ·
                      rfl

theorem cell23_8251959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_8251959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251959 prefixEnd_8251959 := by exact prefixLift 8251959
  have htrace : WordTrace (prefixWord ++ tailWord_8251959) baseStart_8251959 baseEnd_8251959 := by
    simpa [prefixWord, tailWord_8251959, baseEnd_8251959] using wordTrace_append hprefix tailTrace_8251959
  have hstable : (prefixWord ++ tailWord_8251959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251959).length < 2 ^ (prefixWord ++ tailWord_8251959).sum := by decide
  have hdescent : baseEnd_8251959 < baseStart_8251959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251986 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_8251986 : Nat := 118140960795 + 8251986 * 2 ^ 59
def prefixEnd_8251986 : Nat := 4983230072969 + 3 ^ 40 * 8251986 * 2
def baseEnd_8251986 : Nat := 4237235172172656300524813

theorem tailTrace_8251986 : CollatzResearch.WordTrace tailWord_8251986 prefixEnd_8251986 4237235172172656300524813 := by
  unfold tailWord_8251986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75243663870617880962913953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200649770321647682567770541 75243663870617880962913953)
  ·
    refine ⟨56432747902963410722185465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75243663870617880962913953 56432747902963410722185465)
    ·
      refine ⟨42324560927222558041639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56432747902963410722185465 42324560927222558041639099)
      ·
        refine ⟨63486841390833837062458649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42324560927222558041639099 63486841390833837062458649)
        ·
          refine ⟨47615131043125377796843987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63486841390833837062458649 47615131043125377796843987)
          ·
            refine ⟨71422696564688066695265981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47615131043125377796843987 71422696564688066695265981)
            ·
              refine ⟨26783511211758025010724743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71422696564688066695265981 26783511211758025010724743)
              ·
                refine ⟨40175266817637037516087115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26783511211758025010724743 40175266817637037516087115)
                ·
                  refine ⟨60262900226455556274130673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40175266817637037516087115 60262900226455556274130673)
                  ·
                    refine ⟨45197175169841667205598005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60262900226455556274130673 45197175169841667205598005)
                    ·
                      refine ⟨4237235172172656300524813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45197175169841667205598005 4237235172172656300524813)
                      ·
                        rfl

theorem cell23_8251986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_8251986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251986 prefixEnd_8251986 := by exact prefixLift 8251986
  have htrace : WordTrace (prefixWord ++ tailWord_8251986) baseStart_8251986 baseEnd_8251986 := by
    simpa [prefixWord, tailWord_8251986, baseEnd_8251986] using wordTrace_append hprefix tailTrace_8251986
  have hstable : (prefixWord ++ tailWord_8251986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251986).length < 2 ^ (prefixWord ++ tailWord_8251986).sum := by decide
  have hdescent : baseEnd_8251986 < baseStart_8251986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8251999 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_8251999 : Nat := 118140960795 + 8251999 * 2 ^ 59
def prefixEnd_8251999 : Nat := 4983230072969 + 3 ^ 40 * 8251999 * 2
def baseEnd_8251999 : Nat := 4237241847421164749662253

theorem tailTrace_8251999 : CollatzResearch.WordTrace tailWord_8251999 prefixEnd_8251999 4237241847421164749662253 := by
  unfold tailWord_8251999
  simp only [CollatzResearch.WordTrace]
  refine ⟨300975129631424427071879051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200650086420949618047919367 300975129631424427071879051)
  ·
    refine ⟨451462694447136640607818577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300975129631424427071879051 451462694447136640607818577)
    ·
      refine ⟨338597020835352480455863933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451462694447136640607818577 338597020835352480455863933)
      ·
        refine ⟨126973882813257180170948975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338597020835352480455863933 126973882813257180170948975)
        ·
          refine ⟨190460824219885770256423463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126973882813257180170948975 190460824219885770256423463)
          ·
            refine ⟨285691236329828655384635195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190460824219885770256423463 285691236329828655384635195)
            ·
              refine ⟨428536854494742983076952793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285691236329828655384635195 428536854494742983076952793)
              ·
                refine ⟨321402640871057237307714595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428536854494742983076952793 321402640871057237307714595)
                ·
                  refine ⟨482103961306585855961571893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321402640871057237307714595 482103961306585855961571893)
                  ·
                    refine ⟨45197246372492423996397365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 482103961306585855961571893 45197246372492423996397365)
                    ·
                      refine ⟨4237241847421164749662253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45197246372492423996397365 4237241847421164749662253)
                      ·
                        rfl

theorem cell23_8251999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_8251999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8251999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8251999 prefixEnd_8251999 := by exact prefixLift 8251999
  have htrace : WordTrace (prefixWord ++ tailWord_8251999) baseStart_8251999 baseEnd_8251999 := by
    simpa [prefixWord, tailWord_8251999, baseEnd_8251999] using wordTrace_append hprefix tailTrace_8251999
  have hstable : (prefixWord ++ tailWord_8251999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8251999).length < 2 ^ (prefixWord ++ tailWord_8251999).sum := by decide
  have hdescent : baseEnd_8251999 < baseStart_8251999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8251999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252009 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_8252009 : Nat := 118140960795 + 8252009 * 2 ^ 59
def prefixEnd_8252009 : Nat := 4983230072969 + 3 ^ 40 * 8252009 * 2
def baseEnd_8252009 : Nat := 4237246982227709710537207

theorem tailTrace_8252009 : CollatzResearch.WordTrace tailWord_8252009 prefixEnd_8252009 4237246982227709710537207 := by
  unfold tailWord_8252009
  simp only [CollatzResearch.WordTrace]
  refine ⟨300975494361388198779743081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200650329574258799186495387 300975494361388198779743081)
  ·
    refine ⟨225731620771041149084807311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300975494361388198779743081 225731620771041149084807311)
    ·
      refine ⟨338597431156561723627210967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225731620771041149084807311 338597431156561723627210967)
      ·
        refine ⟨507896146734842585440816451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338597431156561723627210967 507896146734842585440816451)
        ·
          refine ⟨761844220102263878161224677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507896146734842585440816451 761844220102263878161224677)
          ·
            refine ⟨142845791269174477155229627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761844220102263878161224677 142845791269174477155229627)
            ·
              refine ⟨214268686903761715732844441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142845791269174477155229627 214268686903761715732844441)
              ·
                refine ⟨160701515177821286799633331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214268686903761715732844441 160701515177821286799633331)
                ·
                  refine ⟨241052272766731930199449997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160701515177821286799633331 241052272766731930199449997)
                  ·
                    refine ⟨90394602287524473824793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241052272766731930199449997 90394602287524473824793749)
                    ·
                      refine ⟨4237246982227709710537207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90394602287524473824793749 4237246982227709710537207)
                      ·
                        rfl

theorem cell23_8252009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_8252009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252009 prefixEnd_8252009 := by exact prefixLift 8252009
  have htrace : WordTrace (prefixWord ++ tailWord_8252009) baseStart_8252009 baseEnd_8252009 := by
    simpa [prefixWord, tailWord_8252009, baseEnd_8252009] using wordTrace_append hprefix tailTrace_8252009
  have hstable : (prefixWord ++ tailWord_8252009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252009).length < 2 ^ (prefixWord ++ tailWord_8252009).sum := by decide
  have hdescent : baseEnd_8252009 < baseStart_8252009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252013 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_8252013 : Nat := 118140960795 + 8252013 * 2 ^ 59
def prefixEnd_8252013 : Nat := 4983230072969 + 3 ^ 40 * 8252013 * 2
def baseEnd_8252013 : Nat := 4237249036150327694887189

theorem tailTrace_8252013 : CollatzResearch.WordTrace tailWord_8252013 prefixEnd_8252013 4237249036150327694887189 := by
  unfold tailWord_8252013
  simp only [CollatzResearch.WordTrace]
  refine ⟨300975640253373707462888693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200650426835582471641925795 300975640253373707462888693)
  ·
    refine ⟨28216466273753785074645815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300975640253373707462888693 28216466273753785074645815)
    ·
      refine ⟨42324699410630677611968723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28216466273753785074645815 42324699410630677611968723)
      ·
        refine ⟨63487049115946016417953085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42324699410630677611968723 63487049115946016417953085)
        ·
          refine ⟨23807643418479756156732407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63487049115946016417953085 23807643418479756156732407)
          ·
            refine ⟨35711465127719634235098611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23807643418479756156732407 35711465127719634235098611)
            ·
              refine ⟨53567197691579451352647917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35711465127719634235098611 53567197691579451352647917)
              ·
                refine ⟨20087699134342294257242969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53567197691579451352647917 20087699134342294257242969)
                ·
                  refine ⟨15065774350756720692932227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20087699134342294257242969 15065774350756720692932227)
                  ·
                    refine ⟨22598661526135081039398341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15065774350756720692932227 22598661526135081039398341)
                    ·
                      refine ⟨4237249036150327694887189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22598661526135081039398341 4237249036150327694887189)
                      ·
                        rfl

theorem cell23_8252013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_8252013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252013 prefixEnd_8252013 := by exact prefixLift 8252013
  have htrace : WordTrace (prefixWord ++ tailWord_8252013) baseStart_8252013 baseEnd_8252013 := by
    simpa [prefixWord, tailWord_8252013, baseEnd_8252013] using wordTrace_append hprefix tailTrace_8252013
  have hstable : (prefixWord ++ tailWord_8252013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252013).length < 2 ^ (prefixWord ++ tailWord_8252013).sum := by decide
  have hdescent : baseEnd_8252013 < baseStart_8252013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252019 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 8]
def baseStart_8252019 : Nat := 118140960795 + 8252019 * 2 ^ 59
def prefixEnd_8252019 : Nat := 4983230072969 + 3 ^ 40 * 8252019 * 2
def baseEnd_8252019 : Nat := 470805790781583852379129

theorem tailTrace_8252019 : CollatzResearch.WordTrace tailWord_8252019 prefixEnd_8252019 470805790781583852379129 := by
  unfold tailWord_8252019
  simp only [CollatzResearch.WordTrace]
  refine ⟨300975859091351970487607111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200650572727567980325071407 300975859091351970487607111)
  ·
    refine ⟨451463788637027955731410667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300975859091351970487607111 451463788637027955731410667)
    ·
      refine ⟨677195682955541933597116001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451463788637027955731410667 677195682955541933597116001)
      ·
        refine ⟨507896762216656450197837001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677195682955541933597116001 507896762216656450197837001)
        ·
          refine ⟨380922571662492337648377751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507896762216656450197837001 380922571662492337648377751)
          ·
            refine ⟨571383857493738506472566627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380922571662492337648377751 571383857493738506472566627)
            ·
              refine ⟨857075786240607759708849941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571383857493738506472566627 857075786240607759708849941)
              ·
                refine ⟨40175427480028488736352341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 857075786240607759708849941 40175427480028488736352341)
                ·
                  refine ⟨470805790781583852379129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40175427480028488736352341 470805790781583852379129)
                  ·
                    rfl

theorem cell23_8252019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 8].length) (baseStart_8252019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252019 prefixEnd_8252019 := by exact prefixLift 8252019
  have htrace : WordTrace (prefixWord ++ tailWord_8252019) baseStart_8252019 baseEnd_8252019 := by
    simpa [prefixWord, tailWord_8252019, baseEnd_8252019] using wordTrace_append hprefix tailTrace_8252019
  have hstable : (prefixWord ++ tailWord_8252019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252019).length < 2 ^ (prefixWord ++ tailWord_8252019).sum := by decide
  have hdescent : baseEnd_8252019 < baseStart_8252019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252033 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_8252033 : Nat := 118140960795 + 8252033 * 2 ^ 59
def prefixEnd_8252033 : Nat := 4983230072969 + 3 ^ 40 * 8252033 * 2
def baseEnd_8252033 : Nat := 4237259305763417616637097

theorem tailTrace_8252033 : CollatzResearch.WordTrace tailWord_8252033 prefixEnd_8252033 4237259305763417616637097 := by
  unfold tailWord_8252033
  simp only [CollatzResearch.WordTrace]
  refine ⟨300976369713301250878616753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200650913142200833919077835 300976369713301250878616753)
  ·
    refine ⟨225732277284975938158962565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300976369713301250878616753 225732277284975938158962565)
    ·
      refine ⟨42324801990932988404805481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225732277284975938158962565 42324801990932988404805481)
      ·
        refine ⟨31743601493199741303604111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42324801990932988404805481 31743601493199741303604111)
        ·
          refine ⟨47615402239799611955406167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31743601493199741303604111 47615402239799611955406167)
          ·
            refine ⟨71423103359699417933109251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47615402239799611955406167 71423103359699417933109251)
            ·
              refine ⟨107134655039549126899663877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71423103359699417933109251 107134655039549126899663877)
              ·
                refine ⟨20087747819915461293686977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107134655039549126899663877 20087747819915461293686977)
                ·
                  refine ⟨15065810864936595970265233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20087747819915461293686977 15065810864936595970265233)
                  ·
                    refine ⟨11299358148702446977698925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15065810864936595970265233 11299358148702446977698925)
                    ·
                      refine ⟨4237259305763417616637097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299358148702446977698925 4237259305763417616637097)
                      ·
                        rfl

theorem cell23_8252033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_8252033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252033 prefixEnd_8252033 := by exact prefixLift 8252033
  have htrace : WordTrace (prefixWord ++ tailWord_8252033) baseStart_8252033 baseEnd_8252033 := by
    simpa [prefixWord, tailWord_8252033, baseEnd_8252033] using wordTrace_append hprefix tailTrace_8252033
  have hstable : (prefixWord ++ tailWord_8252033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252033).length < 2 ^ (prefixWord ++ tailWord_8252033).sum := by decide
  have hdescent : baseEnd_8252033 < baseStart_8252033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252083 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 1, 5]
def baseStart_8252083 : Nat := 118140960795 + 8252083 * 2 ^ 59
def prefixEnd_8252083 : Nat := 4983230072969 + 3 ^ 40 * 8252083 * 2
def baseEnd_8252083 : Nat := 1412428326598714140337289

theorem tailTrace_8252083 : CollatzResearch.WordTrace tailWord_8252083 prefixEnd_8252083 1412428326598714140337289 := by
  unfold tailWord_8252083
  simp only [CollatzResearch.WordTrace]
  refine ⟨300978193363120109417936903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200652128908746739611957935 300978193363120109417936903)
  ·
    refine ⟨451467290044680164126905355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300978193363120109417936903 451467290044680164126905355)
    ·
      refine ⟨677200935067020246190358033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451467290044680164126905355 677200935067020246190358033)
      ·
        refine ⟨507900701300265184642768525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677200935067020246190358033 507900701300265184642768525)
        ·
          refine ⟨190462762987599444241038197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507900701300265184642768525 190462762987599444241038197)
          ·
            refine ⟨17855884030087447897597331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190462762987599444241038197 17855884030087447897597331)
            ·
              refine ⟨26783826045131171846395997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855884030087447897597331 26783826045131171846395997)
              ·
                refine ⟨10043934766924189442398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26783826045131171846395997 10043934766924189442398499)
                ·
                  refine ⟨15065902150386284163597749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043934766924189442398499 15065902150386284163597749)
                  ·
                    refine ⟨1412428326598714140337289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15065902150386284163597749 1412428326598714140337289)
                    ·
                      rfl

theorem cell23_8252083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 5].length) (baseStart_8252083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252083 prefixEnd_8252083 := by exact prefixLift 8252083
  have htrace : WordTrace (prefixWord ++ tailWord_8252083) baseStart_8252083 baseEnd_8252083 := by
    simpa [prefixWord, tailWord_8252083, baseEnd_8252083] using wordTrace_append hprefix tailTrace_8252083
  have hstable : (prefixWord ++ tailWord_8252083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252083).length < 2 ^ (prefixWord ++ tailWord_8252083).sum := by decide
  have hdescent : baseEnd_8252083 < baseStart_8252083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252117 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_8252117 : Nat := 118140960795 + 8252117 * 2 ^ 59
def prefixEnd_8252117 : Nat := 4983230072969 + 3 ^ 40 * 8252117 * 2
def baseEnd_8252117 : Nat := 1412434146046131762662237

theorem tailTrace_8252117 : CollatzResearch.WordTrace tailWord_8252117 prefixEnd_8252117 1412434146046131762662237 := by
  unfold tailWord_8252117
  simp only [CollatzResearch.WordTrace]
  refine ⟨300979433444996933224674605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200652955629997955483116403 300979433444996933224674605)
  ·
    refine ⟨112867287541873849959252977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300979433444996933224674605 112867287541873849959252977)
    ·
      refine ⟨84650465656405387469439733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112867287541873849959252977 84650465656405387469439733)
      ·
        refine ⟨7935981155288005075259975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84650465656405387469439733 7935981155288005075259975)
        ·
          refine ⟨11903971732932007612889963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935981155288005075259975 11903971732932007612889963)
          ·
            refine ⟨17855957599398011419334945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11903971732932007612889963 17855957599398011419334945)
            ·
              refine ⟨13391968199548508564501209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17855957599398011419334945 13391968199548508564501209)
              ·
                refine ⟨10043976149661381423375907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13391968199548508564501209 10043976149661381423375907)
                ·
                  refine ⟨15065964224492072135063861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043976149661381423375907 15065964224492072135063861)
                  ·
                    refine ⟨1412434146046131762662237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15065964224492072135063861 1412434146046131762662237)
                    ·
                      rfl

theorem cell23_8252117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_8252117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252117 prefixEnd_8252117 := by exact prefixLift 8252117
  have htrace : WordTrace (prefixWord ++ tailWord_8252117) baseStart_8252117 baseEnd_8252117 := by
    simpa [prefixWord, tailWord_8252117, baseEnd_8252117] using wordTrace_append hprefix tailTrace_8252117
  have hstable : (prefixWord ++ tailWord_8252117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252117).length < 2 ^ (prefixWord ++ tailWord_8252117).sum := by decide
  have hdescent : baseEnd_8252117 < baseStart_8252117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252120 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_8252120 : Nat := 118140960795 + 8252120 * 2 ^ 59
def prefixEnd_8252120 : Nat := 4983230072969 + 3 ^ 40 * 8252120 * 2
def baseEnd_8252120 : Nat := 4237303978580358776249197

theorem tailTrace_8252120 : CollatzResearch.WordTrace tailWord_8252120 prefixEnd_8252120 4237303978580358776249197 := by
  unfold tailWord_8252120
  simp only [CollatzResearch.WordTrace]
  refine ⟨150489771431993032368516907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200653028575990709824689209 150489771431993032368516907)
  ·
    refine ⟨225734657147989548552775361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150489771431993032368516907 225734657147989548552775361)
    ·
      refine ⟨169300992860992161414581521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225734657147989548552775361 169300992860992161414581521)
      ·
        refine ⟨126975744645744121060936141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169300992860992161414581521 126975744645744121060936141)
        ·
          refine ⟨47615904242154045397851053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126975744645744121060936141 47615904242154045397851053)
          ·
            refine ⟨17855964090807767024194145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47615904242154045397851053 17855964090807767024194145)
            ·
              refine ⟨13391973068105825268145609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17855964090807767024194145 13391973068105825268145609)
              ·
                refine ⟨10043979801079368951109207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13391973068105825268145609 10043979801079368951109207)
                ·
                  refine ⟨15065969701619053426663811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043979801079368951109207 15065969701619053426663811)
                  ·
                    refine ⟨22598954552428580139995717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15065969701619053426663811 22598954552428580139995717)
                    ·
                      refine ⟨4237303978580358776249197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22598954552428580139995717 4237303978580358776249197)
                      ·
                        rfl

theorem cell23_8252120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_8252120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252120 prefixEnd_8252120 := by exact prefixLift 8252120
  have htrace : WordTrace (prefixWord ++ tailWord_8252120) baseStart_8252120 baseEnd_8252120 := by
    simpa [prefixWord, tailWord_8252120, baseEnd_8252120] using wordTrace_append hprefix tailTrace_8252120
  have hstable : (prefixWord ++ tailWord_8252120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252120).length < 2 ^ (prefixWord ++ tailWord_8252120).sum := by decide
  have hdescent : baseEnd_8252120 < baseStart_8252120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252148 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8252148 : Nat := 118140960795 + 8252148 * 2 ^ 59
def prefixEnd_8252148 : Nat := 4983230072969 + 3 ^ 40 * 8252148 * 2
def baseEnd_8252148 : Nat := 4237318356038684666699069

theorem tailTrace_8252148 : CollatzResearch.WordTrace tailWord_8252148 prefixEnd_8252148 4237318356038684666699069 := by
  unfold tailWord_8252148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150490282053942312759526549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200653709405256417012702065 150490282053942312759526549)
  ·
    refine ⟨7054231971278545910602807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150490282053942312759526549 7054231971278545910602807)
    ·
      refine ⟨10581347956917818865904211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054231971278545910602807 10581347956917818865904211)
      ·
        refine ⟨15872021935376728298856317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581347956917818865904211 15872021935376728298856317)
        ·
          refine ⟨5952008225766273112071119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15872021935376728298856317 5952008225766273112071119)
          ·
            refine ⟨8928012338649409668106679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952008225766273112071119 8928012338649409668106679)
            ·
              refine ⟨13392018507974114502160019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928012338649409668106679 13392018507974114502160019)
              ·
                refine ⟨20088027761961171753240029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392018507974114502160019 20088027761961171753240029)
                ·
                  refine ⟨7533010410735439407465011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20088027761961171753240029 7533010410735439407465011)
                  ·
                    refine ⟨11299515616103159111197517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533010410735439407465011 11299515616103159111197517)
                    ·
                      refine ⟨4237318356038684666699069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299515616103159111197517 4237318356038684666699069)
                      ·
                        rfl

theorem cell23_8252148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8252148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252148 prefixEnd_8252148 := by exact prefixLift 8252148
  have htrace : WordTrace (prefixWord ++ tailWord_8252148) baseStart_8252148 baseEnd_8252148 := by
    simpa [prefixWord, tailWord_8252148, baseEnd_8252148] using wordTrace_append hprefix tailTrace_8252148
  have hstable : (prefixWord ++ tailWord_8252148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252148).length < 2 ^ (prefixWord ++ tailWord_8252148).sum := by decide
  have hdescent : baseEnd_8252148 < baseStart_8252148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252163 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 7, 2]
def baseStart_8252163 : Nat := 118140960795 + 8252163 * 2 ^ 59
def prefixEnd_8252163 : Nat := 4983230072969 + 3 ^ 40 * 8252163 * 2
def baseEnd_8252163 : Nat := 4237326058248502108011499

theorem tailTrace_8252163 : CollatzResearch.WordTrace tailWord_8252163 prefixEnd_8252163 4237326058248502108011499 := by
  unfold tailWord_8252163
  simp only [CollatzResearch.WordTrace]
  refine ⟨300981111202830283080849143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200654074135220188720566095 300981111202830283080849143)
  ·
    refine ⟨451471666804245424621273715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300981111202830283080849143 451471666804245424621273715)
    ·
      refine ⟨677207500206368136931910573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451471666804245424621273715 677207500206368136931910573)
      ·
        refine ⟨253952812577388051349466465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677207500206368136931910573 253952812577388051349466465)
        ·
          refine ⟨190464609433041038512099849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253952812577388051349466465 190464609433041038512099849)
          ·
            refine ⟨142848457074780778884074887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190464609433041038512099849 142848457074780778884074887)
            ·
              refine ⟨214272685612171168326112331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142848457074780778884074887 214272685612171168326112331)
              ·
                refine ⟨321409028418256752489168497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214272685612171168326112331 321409028418256752489168497)
                ·
                  refine ⟨241056771313692564366876373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321409028418256752489168497 241056771313692564366876373)
                  ·
                    refine ⟨5649768077664669477348665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241056771313692564366876373 5649768077664669477348665)
                    ·
                      refine ⟨4237326058248502108011499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649768077664669477348665 4237326058248502108011499)
                      ·
                        rfl

theorem cell23_8252163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_8252163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252163 prefixEnd_8252163 := by exact prefixLift 8252163
  have htrace : WordTrace (prefixWord ++ tailWord_8252163) baseStart_8252163 baseEnd_8252163 := by
    simpa [prefixWord, tailWord_8252163, baseEnd_8252163] using wordTrace_append hprefix tailTrace_8252163
  have hstable : (prefixWord ++ tailWord_8252163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252163).length < 2 ^ (prefixWord ++ tailWord_8252163).sum := by decide
  have hdescent : baseEnd_8252163 < baseStart_8252163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252210 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_8252210 : Nat := 118140960795 + 8252210 * 2 ^ 59
def prefixEnd_8252210 : Nat := 4983230072969 + 3 ^ 40 * 8252210 * 2
def baseEnd_8252210 : Nat := 4237350191839263424123783

theorem tailTrace_8252210 : CollatzResearch.WordTrace tailWord_8252210 prefixEnd_8252210 4237350191839263424123783 := by
  unfold tailWord_8252210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75245706358415002526952521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200655216955773340071873389 75245706358415002526952521)
  ·
    refine ⟨56434279768811251895214391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75245706358415002526952521 56434279768811251895214391)
    ·
      refine ⟨84651419653216877842821587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56434279768811251895214391 84651419653216877842821587)
      ·
        refine ⟨126977129479825316764232381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84651419653216877842821587 126977129479825316764232381)
        ·
          refine ⟨47616423554934493786587143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126977129479825316764232381 47616423554934493786587143)
          ·
            refine ⟨71424635332401740679880715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47616423554934493786587143 71424635332401740679880715)
            ·
              refine ⟨107136952998602611019821073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71424635332401740679880715 107136952998602611019821073)
              ·
                refine ⟨80352714748951958264865805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107136952998602611019821073 80352714748951958264865805)
                ·
                  refine ⟨30132268030856984349324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80352714748951958264865805 30132268030856984349324677)
                  ·
                    refine ⟨5649800255785684565498377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30132268030856984349324677 5649800255785684565498377)
                    ·
                      refine ⟨4237350191839263424123783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649800255785684565498377 4237350191839263424123783)
                      ·
                        rfl

theorem cell23_8252210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_8252210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252210 prefixEnd_8252210 := by exact prefixLift 8252210
  have htrace : WordTrace (prefixWord ++ tailWord_8252210) baseStart_8252210 baseEnd_8252210 := by
    simpa [prefixWord, tailWord_8252210, baseEnd_8252210] using wordTrace_append hprefix tailTrace_8252210
  have hstable : (prefixWord ++ tailWord_8252210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252210).length < 2 ^ (prefixWord ++ tailWord_8252210).sum := by decide
  have hdescent : baseEnd_8252210 < baseStart_8252210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252223 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_8252223 : Nat := 118140960795 + 8252223 * 2 ^ 59
def prefixEnd_8252223 : Nat := 4983230072969 + 3 ^ 40 * 8252223 * 2
def baseEnd_8252223 : Nat := 4237356867087771873261223

theorem tailTrace_8252223 : CollatzResearch.WordTrace tailWord_8252223 prefixEnd_8252223 4237356867087771873261223 := by
  unfold tailWord_8252223
  simp only [CollatzResearch.WordTrace]
  refine ⟨300983299582612913328033323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200655533055075275552022215 300983299582612913328033323)
  ·
    refine ⟨451474949373919369992049985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300983299582612913328033323 451474949373919369992049985)
    ·
      refine ⟨338606212030439527494037489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451474949373919369992049985 338606212030439527494037489)
      ·
        refine ⟨253954659022829645620528117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338606212030439527494037489 253954659022829645620528117)
        ·
          refine ⟨23808249283390279276924511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253954659022829645620528117 23808249283390279276924511)
          ·
            refine ⟨35712373925085418915386767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23808249283390279276924511 35712373925085418915386767)
            ·
              refine ⟨53568560887628128373080151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35712373925085418915386767 53568560887628128373080151)
              ·
                refine ⟨80352841331442192559620227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53568560887628128373080151 80352841331442192559620227)
                ·
                  refine ⟨120529261997163288839430341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80352841331442192559620227 120529261997163288839430341)
                  ·
                    refine ⟨22599236624468116657393189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120529261997163288839430341 22599236624468116657393189)
                    ·
                      refine ⟨4237356867087771873261223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22599236624468116657393189 4237356867087771873261223)
                      ·
                        rfl

theorem cell23_8252223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_8252223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252223 prefixEnd_8252223 := by exact prefixLift 8252223
  have htrace : WordTrace (prefixWord ++ tailWord_8252223) baseStart_8252223 baseEnd_8252223 := by
    simpa [prefixWord, tailWord_8252223, baseEnd_8252223] using wordTrace_append hprefix tailTrace_8252223
  have hstable : (prefixWord ++ tailWord_8252223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252223).length < 2 ^ (prefixWord ++ tailWord_8252223).sum := by decide
  have hdescent : baseEnd_8252223 < baseStart_8252223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252227 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 2, 2, 2]
def baseStart_8252227 : Nat := 118140960795 + 8252227 * 2 ^ 59
def prefixEnd_8252227 : Nat := 4983230072969 + 3 ^ 40 * 8252227 * 2
def baseEnd_8252227 : Nat := 4237358921010389857611205

theorem tailTrace_8252227 : CollatzResearch.WordTrace tailWord_8252227 prefixEnd_8252227 4237358921010389857611205 := by
  unfold tailWord_8252227
  simp only [CollatzResearch.WordTrace]
  refine ⟨300983445474598422011178935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200655630316398948007452623 300983445474598422011178935)
  ·
    refine ⟨451475168211897633016768403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300983445474598422011178935 451475168211897633016768403)
    ·
      refine ⟨677212752317846449525152605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451475168211897633016768403 677212752317846449525152605)
      ·
        refine ⟨253954782119192418571932227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677212752317846449525152605 253954782119192418571932227)
        ·
          refine ⟨380932173178788627857898341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253954782119192418571932227 380932173178788627857898341)
          ·
            refine ⟨71424782471022867723355939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380932173178788627857898341 71424782471022867723355939)
            ·
              refine ⟨107137173706534301585033909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71424782471022867723355939 107137173706534301585033909)
              ·
                refine ⟨10044110034987590773596929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107137173706534301585033909 10044110034987590773596929)
                ·
                  refine ⟨7533082526240693080197697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044110034987590773596929 7533082526240693080197697)
                  ·
                    refine ⟨5649811894680519810148273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533082526240693080197697 5649811894680519810148273)
                    ·
                      refine ⟨4237358921010389857611205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649811894680519810148273 4237358921010389857611205)
                      ·
                        rfl

theorem cell23_8252227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_8252227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252227 prefixEnd_8252227 := by exact prefixLift 8252227
  have htrace : WordTrace (prefixWord ++ tailWord_8252227) baseStart_8252227 baseEnd_8252227 := by
    simpa [prefixWord, tailWord_8252227, baseEnd_8252227] using wordTrace_append hprefix tailTrace_8252227
  have hstable : (prefixWord ++ tailWord_8252227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252227).length < 2 ^ (prefixWord ++ tailWord_8252227).sum := by decide
  have hdescent : baseEnd_8252227 < baseStart_8252227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252233 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 7]
def baseStart_8252233 : Nat := 118140960795 + 8252233 * 2 ^ 59
def prefixEnd_8252233 : Nat := 4983230072969 + 3 ^ 40 * 8252233 * 2
def baseEnd_8252233 : Nat := 470818000210479648237353

theorem tailTrace_8252233 : CollatzResearch.WordTrace tailWord_8252233 prefixEnd_8252233 470818000210479648237353 := by
  unfold tailWord_8252233
  simp only [CollatzResearch.WordTrace]
  refine ⟨300983664312576685035897353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200655776208384456690598235 300983664312576685035897353)
  ·
    refine ⟨225737748234432513776923015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300983664312576685035897353 225737748234432513776923015)
    ·
      refine ⟨338606622351648770665384523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225737748234432513776923015 338606622351648770665384523)
      ·
        refine ⟨507909933527473155998076785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338606622351648770665384523 507909933527473155998076785)
        ·
          refine ⟨380932450145604866998557589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507909933527473155998076785 380932450145604866998557589)
          ·
            refine ⟨17856208600575228140557387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380932450145604866998557589 17856208600575228140557387)
            ·
              refine ⟨26784312900862842210836081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17856208600575228140557387 26784312900862842210836081)
              ·
                refine ⟨20088234675647131658127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26784312900862842210836081 20088234675647131658127061)
                ·
                  refine ⟨470818000210479648237353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20088234675647131658127061 470818000210479648237353)
                  ·
                    rfl

theorem cell23_8252233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_8252233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252233 prefixEnd_8252233 := by exact prefixLift 8252233
  have htrace : WordTrace (prefixWord ++ tailWord_8252233) baseStart_8252233 baseEnd_8252233 := by
    simpa [prefixWord, tailWord_8252233, baseEnd_8252233] using wordTrace_append hprefix tailTrace_8252233
  have hstable : (prefixWord ++ tailWord_8252233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252233).length < 2 ^ (prefixWord ++ tailWord_8252233).sum := by decide
  have hdescent : baseEnd_8252233 < baseStart_8252233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252250 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_8252250 : Nat := 118140960795 + 8252250 * 2 ^ 59
def prefixEnd_8252250 : Nat := 4983230072969 + 3 ^ 40 * 8252250 * 2
def baseEnd_8252250 : Nat := 470818970118382585291511

theorem tailTrace_8252250 : CollatzResearch.WordTrace tailWord_8252250 prefixEnd_8252250 470818970118382585291511 := by
  unfold tailWord_8252250
  simp only [CollatzResearch.WordTrace]
  refine ⟨75246071088378774234816551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200656189569010064626177469 75246071088378774234816551)
  ·
    refine ⟨112869106632568161352224827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75246071088378774234816551 112869106632568161352224827)
    ·
      refine ⟨169303659948852242028337241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112869106632568161352224827 169303659948852242028337241)
      ·
        refine ⟨126977744961639181521252931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169303659948852242028337241 126977744961639181521252931)
        ·
          refine ⟨190466617442458772281879397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126977744961639181521252931 190466617442458772281879397)
          ·
            refine ⟨35712490770461019802852387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190466617442458772281879397 35712490770461019802852387)
            ·
              refine ⟨53568736155691529704278581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35712490770461019802852387 53568736155691529704278581)
              ·
                refine ⟨5022069014596080909776117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53568736155691529704278581 5022069014596080909776117)
                ·
                  refine ⟨470818970118382585291511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022069014596080909776117 470818970118382585291511)
                  ·
                    rfl

theorem cell23_8252250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_8252250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252250 prefixEnd_8252250 := by exact prefixLift 8252250
  have htrace : WordTrace (prefixWord ++ tailWord_8252250) baseStart_8252250 baseEnd_8252250 := by
    simpa [prefixWord, tailWord_8252250, baseEnd_8252250] using wordTrace_append hprefix tailTrace_8252250
  have hstable : (prefixWord ++ tailWord_8252250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252250).length < 2 ^ (prefixWord ++ tailWord_8252250).sum := by decide
  have hdescent : baseEnd_8252250 < baseStart_8252250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252260 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_8252260 : Nat := 118140960795 + 8252260 * 2 ^ 59
def prefixEnd_8252260 : Nat := 4983230072969 + 3 ^ 40 * 8252260 * 2
def baseEnd_8252260 : Nat := 4237375865871988228498553

theorem tailTrace_8252260 : CollatzResearch.WordTrace tailWord_8252260 prefixEnd_8252260 4237375865871988228498553 := by
  unfold tailWord_8252260
  simp only [CollatzResearch.WordTrace]
  refine ⟨150492324541739434323565117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200656432722319245764753489 150492324541739434323565117)
  ·
    refine ⟨56434621703152287871336919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150492324541739434323565117 56434621703152287871336919)
    ·
      refine ⟨84651932554728431807005379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56434621703152287871336919 84651932554728431807005379)
      ·
        refine ⟨126977898832092647710508069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84651932554728431807005379 126977898832092647710508069)
        ·
          refine ⟨23808356031017371445720263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126977898832092647710508069 23808356031017371445720263)
          ·
            refine ⟨35712534046526057168580395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23808356031017371445720263 35712534046526057168580395)
            ·
              refine ⟨53568801069789085752870593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35712534046526057168580395 53568801069789085752870593)
              ·
                refine ⟨40176600802341814314652945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53568801069789085752870593 40176600802341814314652945)
                ·
                  refine ⟨30132450601756360735989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40176600802341814314652945 30132450601756360735989709)
                  ·
                    refine ⟨11299668975658635275996141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30132450601756360735989709 11299668975658635275996141)
                    ·
                      refine ⟨4237375865871988228498553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299668975658635275996141 4237375865871988228498553)
                      ·
                        rfl

theorem cell23_8252260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_8252260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252260 prefixEnd_8252260 := by exact prefixLift 8252260
  have htrace : WordTrace (prefixWord ++ tailWord_8252260) baseStart_8252260 baseEnd_8252260 := by
    simpa [prefixWord, tailWord_8252260, baseEnd_8252260] using wordTrace_append hprefix tailTrace_8252260
  have hstable : (prefixWord ++ tailWord_8252260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252260).length < 2 ^ (prefixWord ++ tailWord_8252260).sum := by decide
  have hdescent : baseEnd_8252260 < baseStart_8252260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252278 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_8252278 : Nat := 118140960795 + 8252278 * 2 ^ 59
def prefixEnd_8252278 : Nat := 4983230072969 + 3 ^ 40 * 8252278 * 2
def baseEnd_8252278 : Nat := 4237385108523769158073471

theorem tailTrace_8252278 : CollatzResearch.WordTrace tailWord_8252278 prefixEnd_8252278 4237385108523769158073471 := by
  unfold tailWord_8252278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18811581599838353607580343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200656870398275771814190325 18811581599838353607580343)
  ·
    refine ⟨28217372399757530411370515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18811581599838353607580343 28217372399757530411370515)
    ·
      refine ⟨42326058599636295617055773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28217372399757530411370515 42326058599636295617055773)
      ·
        refine ⟨15872271974863610856395915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42326058599636295617055773 15872271974863610856395915)
        ·
          refine ⟨23808407962295416284593873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15872271974863610856395915 23808407962295416284593873)
          ·
            refine ⟨17856305971721562213445405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23808407962295416284593873 17856305971721562213445405)
            ·
              refine ⟨6696114739395585830042027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17856305971721562213445405 6696114739395585830042027)
              ·
                refine ⟨10044172109093378745063041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696114739395585830042027 10044172109093378745063041)
                ·
                  refine ⟨7533129081820034058797281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044172109093378745063041 7533129081820034058797281)
                  ·
                    refine ⟨5649846811365025544097961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533129081820034058797281 5649846811365025544097961)
                    ·
                      refine ⟨4237385108523769158073471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649846811365025544097961 4237385108523769158073471)
                      ·
                        rfl

theorem cell23_8252278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_8252278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252278 prefixEnd_8252278 := by exact prefixLift 8252278
  have htrace : WordTrace (prefixWord ++ tailWord_8252278) baseStart_8252278 baseEnd_8252278 := by
    simpa [prefixWord, tailWord_8252278, baseEnd_8252278] using wordTrace_append hprefix tailTrace_8252278
  have hstable : (prefixWord ++ tailWord_8252278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252278).length < 2 ^ (prefixWord ++ tailWord_8252278).sum := by decide
  have hdescent : baseEnd_8252278 < baseStart_8252278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252283 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_8252283 : Nat := 118140960795 + 8252283 * 2 ^ 59
def prefixEnd_8252283 : Nat := 4983230072969 + 3 ^ 40 * 8252283 * 2
def baseEnd_8252283 : Nat := 4237387675927041638510947

theorem tailTrace_8252283 : CollatzResearch.WordTrace tailWord_8252283 prefixEnd_8252283 4237387675927041638510947 := by
  unfold tailWord_8252283
  simp only [CollatzResearch.WordTrace]
  refine ⟨300985487962395543575217503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200656991974930362383478335 300985487962395543575217503)
  ·
    refine ⟨451478231943593315362826255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300985487962395543575217503 451478231943593315362826255)
    ·
      refine ⟨677217347915389973044239383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451478231943593315362826255 677217347915389973044239383)
      ·
        refine ⟨1015826021873084959566359075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677217347915389973044239383 1015826021873084959566359075)
        ·
          refine ⟨1523739032809627439349538613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015826021873084959566359075 1523739032809627439349538613)
          ·
            refine ⟨142850534325902572439019245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1523739032809627439349538613 142850534325902572439019245)
            ·
              refine ⟨53568950372213464664632217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142850534325902572439019245 53568950372213464664632217)
              ·
                refine ⟨40176712779160098498474163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53568950372213464664632217 40176712779160098498474163)
                ·
                  refine ⟨60265069168740147747711245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40176712779160098498474163 60265069168740147747711245)
                  ·
                    refine ⟨22599400938277555405391717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60265069168740147747711245 22599400938277555405391717)
                    ·
                      refine ⟨4237387675927041638510947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22599400938277555405391717 4237387675927041638510947)
                      ·
                        rfl

theorem cell23_8252283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_8252283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252283 prefixEnd_8252283 := by exact prefixLift 8252283
  have htrace : WordTrace (prefixWord ++ tailWord_8252283) baseStart_8252283 baseEnd_8252283 := by
    simpa [prefixWord, tailWord_8252283, baseEnd_8252283] using wordTrace_append hprefix tailTrace_8252283
  have hstable : (prefixWord ++ tailWord_8252283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252283).length < 2 ^ (prefixWord ++ tailWord_8252283).sum := by decide
  have hdescent : baseEnd_8252283 < baseStart_8252283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252300 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_8252300 : Nat := 118140960795 + 8252300 * 2 ^ 59
def prefixEnd_8252300 : Nat := 4983230072969 + 3 ^ 40 * 8252300 * 2
def baseEnd_8252300 : Nat := 4237396405098168071998369

theorem tailTrace_8252300 : CollatzResearch.WordTrace tailWord_8252300 prefixEnd_8252300 4237396405098168071998369 := by
  unfold tailWord_8252300
  simp only [CollatzResearch.WordTrace]
  refine ⟨150493054001666977739293177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200657405335555970319057569 150493054001666977739293177)
  ·
    refine ⟨112869790501250233304469883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150493054001666977739293177 112869790501250233304469883)
    ·
      refine ⟨169304685751875349956704825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112869790501250233304469883 169304685751875349956704825)
      ·
        refine ⟨126978514313906512467528619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169304685751875349956704825 126978514313906512467528619)
        ·
          refine ⟨190467771470859768701292929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126978514313906512467528619 190467771470859768701292929)
          ·
            refine ⟨142850828603144826525969697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190467771470859768701292929 142850828603144826525969697)
            ·
              refine ⟨107138121452358619894477273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142850828603144826525969697 107138121452358619894477273)
              ·
                refine ⟨80353591089268964920857955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107138121452358619894477273 80353591089268964920857955)
                ·
                  refine ⟨120530386633903447381286933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80353591089268964920857955 120530386633903447381286933)
                  ·
                    refine ⟨5649861873464224095997825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120530386633903447381286933 5649861873464224095997825)
                    ·
                      refine ⟨4237396405098168071998369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649861873464224095997825 4237396405098168071998369)
                      ·
                        rfl

theorem cell23_8252300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_8252300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252300 prefixEnd_8252300 := by exact prefixLift 8252300
  have htrace : WordTrace (prefixWord ++ tailWord_8252300) baseStart_8252300 baseEnd_8252300 := by
    simpa [prefixWord, tailWord_8252300, baseEnd_8252300] using wordTrace_append hprefix tailTrace_8252300
  have hstable : (prefixWord ++ tailWord_8252300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252300).length < 2 ^ (prefixWord ++ tailWord_8252300).sum := by decide
  have hdescent : baseEnd_8252300 < baseStart_8252300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252320 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_8252320 : Nat := 118140960795 + 8252320 * 2 ^ 59
def prefixEnd_8252320 : Nat := 4983230072969 + 3 ^ 40 * 8252320 * 2
def baseEnd_8252320 : Nat := 4237406674711257993748277

theorem tailTrace_8252320 : CollatzResearch.WordTrace tailWord_8252320 prefixEnd_8252320 4237406674711257993748277 := by
  unfold tailWord_8252320
  simp only [CollatzResearch.WordTrace]
  refine ⟨150493418731630749447157207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200657891642174332596209609 150493418731630749447157207)
  ·
    refine ⟨225740128097446124170735811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150493418731630749447157207 225740128097446124170735811)
    ·
      refine ⟨338610192146169186256103717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225740128097446124170735811 338610192146169186256103717)
      ·
        refine ⟨63489411027406722423019447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338610192146169186256103717 63489411027406722423019447)
        ·
          refine ⟨95234116541110083634529171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63489411027406722423019447 95234116541110083634529171)
          ·
            refine ⟨142851174811665125451793757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95234116541110083634529171 142851174811665125451793757)
            ·
              refine ⟨53569190554374422044422659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142851174811665125451793757 53569190554374422044422659)
              ·
                refine ⟨80353785831561633066633989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53569190554374422044422659 80353785831561633066633989)
                ·
                  refine ⟨15066334843417806199993873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80353785831561633066633989 15066334843417806199993873)
                  ·
                    refine ⟨11299751132563354649995405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15066334843417806199993873 11299751132563354649995405)
                    ·
                      refine ⟨4237406674711257993748277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11299751132563354649995405 4237406674711257993748277)
                      ·
                        rfl

theorem cell23_8252320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_8252320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252320 prefixEnd_8252320 := by exact prefixLift 8252320
  have htrace : WordTrace (prefixWord ++ tailWord_8252320) baseStart_8252320 baseEnd_8252320 := by
    simpa [prefixWord, tailWord_8252320, baseEnd_8252320] using wordTrace_append hprefix tailTrace_8252320
  have hstable : (prefixWord ++ tailWord_8252320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252320).length < 2 ^ (prefixWord ++ tailWord_8252320).sum := by decide
  have hdescent : baseEnd_8252320 < baseStart_8252320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252323 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 8]
def baseStart_8252323 : Nat := 118140960795 + 8252323 * 2 ^ 59
def prefixEnd_8252323 : Nat := 4983230072969 + 3 ^ 40 * 8252323 * 2
def baseEnd_8252323 : Nat := 470823135017024609112307

theorem tailTrace_8252323 : CollatzResearch.WordTrace tailWord_8252323 prefixEnd_8252323 470823135017024609112307 := by
  unfold tailWord_8252323
  simp only [CollatzResearch.WordTrace]
  refine ⟨300986946882250630406673623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200657964588167086937782415 300986946882250630406673623)
  ·
    refine ⟨451480420323375945610010435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300986946882250630406673623 451480420323375945610010435)
    ·
      refine ⟨677220630485063918415015653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451480420323375945610010435 677220630485063918415015653)
      ·
        refine ⟨126978868215949484702815435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677220630485063918415015653 126978868215949484702815435)
        ·
          refine ⟨190468302323924227054223153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126978868215949484702815435 190468302323924227054223153)
          ·
            refine ⟨142851226742943170290667365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190468302323924227054223153 142851226742943170290667365)
            ·
              refine ⟨26784605014301844429500131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142851226742943170290667365 26784605014301844429500131)
              ·
                refine ⟨40176907521452766644250197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26784605014301844429500131 40176907521452766644250197)
                ·
                  refine ⟨470823135017024609112307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40176907521452766644250197 470823135017024609112307)
                  ·
                    rfl

theorem cell23_8252323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 8].length) (baseStart_8252323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252323 prefixEnd_8252323 := by exact prefixLift 8252323
  have htrace : WordTrace (prefixWord ++ tailWord_8252323) baseStart_8252323 baseEnd_8252323 := by
    simpa [prefixWord, tailWord_8252323, baseEnd_8252323] using wordTrace_append hprefix tailTrace_8252323
  have hstable : (prefixWord ++ tailWord_8252323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252323).length < 2 ^ (prefixWord ++ tailWord_8252323).sum := by decide
  have hdescent : baseEnd_8252323 < baseStart_8252323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252343 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_8252343 : Nat := 118140960795 + 8252343 * 2 ^ 59
def prefixEnd_8252343 : Nat := 4983230072969 + 3 ^ 40 * 8252343 * 2
def baseEnd_8252343 : Nat := 4237418484766311403760671

theorem tailTrace_8252343 : CollatzResearch.WordTrace tailWord_8252343 prefixEnd_8252343 4237418484766311403760671 := by
  unfold tailWord_8252343
  simp only [CollatzResearch.WordTrace]
  refine ⟨300987676342178173822401683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200658450894785449214934455 300987676342178173822401683)
  ·
    refine ⟨451481514513267260733602525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300987676342178173822401683 451481514513267260733602525)
    ·
      refine ⟨169305567942475222775100947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451481514513267260733602525 169305567942475222775100947)
      ·
        refine ⟨253958351913712834162651421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169305567942475222775100947 253958351913712834162651421)
        ·
          refine ⟨95234381967642312810994283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253958351913712834162651421 95234381967642312810994283)
          ·
            refine ⟨142851572951463469216491425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95234381967642312810994283 142851572951463469216491425)
            ·
              refine ⟨107138679713597601912368569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142851572951463469216491425 107138679713597601912368569)
              ·
                refine ⟨80354009785198201434276427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107138679713597601912368569 80354009785198201434276427)
                ·
                  refine ⟨120531014677797302151414641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80354009785198201434276427 120531014677797302151414641)
                  ·
                    refine ⟨90398261008347976613560981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120531014677797302151414641 90398261008347976613560981)
                    ·
                      refine ⟨4237418484766311403760671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90398261008347976613560981 4237418484766311403760671)
                      ·
                        rfl

theorem cell23_8252343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_8252343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252343 prefixEnd_8252343 := by exact prefixLift 8252343
  have htrace : WordTrace (prefixWord ++ tailWord_8252343) baseStart_8252343 baseEnd_8252343 := by
    simpa [prefixWord, tailWord_8252343, baseEnd_8252343] using wordTrace_append hprefix tailTrace_8252343
  have hstable : (prefixWord ++ tailWord_8252343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252343).length < 2 ^ (prefixWord ++ tailWord_8252343).sum := by decide
  have hdescent : baseEnd_8252343 < baseStart_8252343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252374 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_8252374 : Nat := 118140960795 + 8252374 * 2 ^ 59
def prefixEnd_8252374 : Nat := 4983230072969 + 3 ^ 40 * 8252374 * 2
def baseEnd_8252374 : Nat := 470826044740733420274781

theorem tailTrace_8252374 : CollatzResearch.WordTrace tailWord_8252374 prefixEnd_8252374 470826044740733420274781 := by
  unfold tailWord_8252374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18811800437816616632298761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200659204670043910744520117 18811800437816616632298761)
  ·
    refine ⟨14108850328362462474224071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18811800437816616632298761 14108850328362462474224071)
    ·
      refine ⟨21163275492543693711336107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14108850328362462474224071 21163275492543693711336107)
      ·
        refine ⟨31744913238815540567004161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21163275492543693711336107 31744913238815540567004161)
        ·
          refine ⟨23808684929111655425253121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31744913238815540567004161 23808684929111655425253121)
          ·
            refine ⟨17856513696833741568939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23808684929111655425253121 17856513696833741568939841)
            ·
              refine ⟨13392385272625306176704881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17856513696833741568939841 13392385272625306176704881)
              ·
                refine ⟨10044288954468979632528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13392385272625306176704881 10044288954468979632528661)
                ·
                  refine ⟨470826044740733420274781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10044288954468979632528661 470826044740733420274781)
                  ·
                    rfl

theorem cell23_8252374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_8252374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252374 prefixEnd_8252374 := by exact prefixLift 8252374
  have htrace : WordTrace (prefixWord ++ tailWord_8252374) baseStart_8252374 baseEnd_8252374 := by
    simpa [prefixWord, tailWord_8252374, baseEnd_8252374] using wordTrace_append hprefix tailTrace_8252374
  have hstable : (prefixWord ++ tailWord_8252374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252374).length < 2 ^ (prefixWord ++ tailWord_8252374).sum := by decide
  have hdescent : baseEnd_8252374 < baseStart_8252374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252400 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_8252400 : Nat := 118140960795 + 8252400 * 2 ^ 59
def prefixEnd_8252400 : Nat := 4983230072969 + 3 ^ 40 * 8252400 * 2
def baseEnd_8252400 : Nat := 1412482584387872560249303

theorem tailTrace_8252400 : CollatzResearch.WordTrace tailWord_8252400 prefixEnd_8252400 1412482584387872560249303 := by
  unfold tailWord_8252400
  simp only [CollatzResearch.WordTrace]
  refine ⟨150494877651485836278613327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200659836868647781704817769 150494877651485836278613327)
  ·
    refine ⟨225742316477228754417919991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150494877651485836278613327 225742316477228754417919991)
    ·
      refine ⟨338613474715843131626879987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225742316477228754417919991 338613474715843131626879987)
      ·
        refine ⟨507920212073764697440319981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338613474715843131626879987 507920212073764697440319981)
        ·
          refine ⟨190470079527661761540119993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507920212073764697440319981 190470079527661761540119993)
          ·
            refine ⟨142852559645746321155089995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190470079527661761540119993 142852559645746321155089995)
            ·
              refine ⟨214278839468619481732634993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142852559645746321155089995 214278839468619481732634993)
              ·
                refine ⟨160709129601464611299476245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214278839468619481732634993 160709129601464611299476245)
                ·
                  refine ⟨7533240450068653654662949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160709129601464611299476245 7533240450068653654662949)
                  ·
                    refine ⟨1412482584387872560249303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533240450068653654662949 1412482584387872560249303)
                    ·
                      rfl

theorem cell23_8252400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_8252400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252400 prefixEnd_8252400 := by exact prefixLift 8252400
  have htrace : WordTrace (prefixWord ++ tailWord_8252400) baseStart_8252400 baseEnd_8252400 := by
    simpa [prefixWord, tailWord_8252400, baseEnd_8252400] using wordTrace_append hprefix tailTrace_8252400
  have hstable : (prefixWord ++ tailWord_8252400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252400).length < 2 ^ (prefixWord ++ tailWord_8252400).sum := by decide
  have hdescent : baseEnd_8252400 < baseStart_8252400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252424 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_8252424 : Nat := 118140960795 + 8252424 * 2 ^ 59
def prefixEnd_8252424 : Nat := 4983230072969 + 3 ^ 40 * 8252424 * 2
def baseEnd_8252424 : Nat := 4237460076699325586847799

theorem tailTrace_8252424 : CollatzResearch.WordTrace tailWord_8252424 prefixEnd_8252424 4237460076699325586847799 := by
  unfold tailWord_8252424
  simp only [CollatzResearch.WordTrace]
  refine ⟨150495315327442362328050163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200660420436589816437400217 150495315327442362328050163)
  ·
    refine ⟨225742972991163543492075245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150495315327442362328050163 225742972991163543492075245)
    ·
      refine ⟨84653614871686328809528217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225742972991163543492075245 84653614871686328809528217)
      ·
        refine ⟨63490211153764746607146163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84653614871686328809528217 63490211153764746607146163)
        ·
          refine ⟨95235316730647119910719245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63490211153764746607146163 95235316730647119910719245)
          ·
            refine ⟨35713243773992669966519717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95235316730647119910719245 35713243773992669966519717)
            ·
              refine ⟨6696233207623625618722447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35713243773992669966519717 6696233207623625618722447)
              ·
                refine ⟨10044349811435438428083671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696233207623625618722447 10044349811435438428083671)
                ·
                  refine ⟨15066524717153157642125507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10044349811435438428083671 15066524717153157642125507)
                  ·
                    refine ⟨22599787075729736463188261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15066524717153157642125507 22599787075729736463188261)
                    ·
                      refine ⟨4237460076699325586847799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22599787075729736463188261 4237460076699325586847799)
                      ·
                        rfl

theorem cell23_8252424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_8252424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252424 prefixEnd_8252424 := by exact prefixLift 8252424
  have htrace : WordTrace (prefixWord ++ tailWord_8252424) baseStart_8252424 baseEnd_8252424 := by
    simpa [prefixWord, tailWord_8252424, baseEnd_8252424] using wordTrace_append hprefix tailTrace_8252424
  have hstable : (prefixWord ++ tailWord_8252424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252424).length < 2 ^ (prefixWord ++ tailWord_8252424).sum := by decide
  have hdescent : baseEnd_8252424 < baseStart_8252424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252430 : List Nat := [4, 1, 1, 2, 2, 3, 10]
def baseStart_8252430 : Nat := 118140960795 + 8252430 * 2 ^ 59
def prefixEnd_8252430 : Nat := 4983230072969 + 3 ^ 40 * 8252430 * 2
def baseEnd_8252430 : Nat := 52314359970163611893491

theorem tailTrace_8252430 : CollatzResearch.WordTrace tailWord_8252430 prefixEnd_8252430 52314359970163611893491 := by
  unfold tailWord_8252430
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623856186607873460102343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200660566328575325120545829 37623856186607873460102343)
  ·
    refine ⟨56435784279911810190153515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623856186607873460102343 56435784279911810190153515)
    ·
      refine ⟨84653676419867715285230273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56435784279911810190153515 84653676419867715285230273)
      ·
        refine ⟨63490257314900786463922705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84653676419867715285230273 63490257314900786463922705)
        ·
          refine ⟨47617692986175589847942029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63490257314900786463922705 47617692986175589847942029)
          ·
            refine ⟨17856634869815846192978261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47617692986175589847942029 17856634869815846192978261)
            ·
              refine ⟨52314359970163611893491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17856634869815846192978261 52314359970163611893491)
              ·
                rfl

theorem cell23_8252430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 10].length) (baseStart_8252430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252430 prefixEnd_8252430 := by exact prefixLift 8252430
  have htrace : WordTrace (prefixWord ++ tailWord_8252430) baseStart_8252430 baseEnd_8252430 := by
    simpa [prefixWord, tailWord_8252430, baseEnd_8252430] using wordTrace_append hprefix tailTrace_8252430
  have hstable : (prefixWord ++ tailWord_8252430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252430).length < 2 ^ (prefixWord ++ tailWord_8252430).sum := by decide
  have hdescent : baseEnd_8252430 < baseStart_8252430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252441 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 1, 2, 2]
def baseStart_8252441 : Nat := 118140960795 + 8252441 * 2 ^ 59
def prefixEnd_8252441 : Nat := 4983230072969 + 3 ^ 40 * 8252441 * 2
def baseEnd_8252441 : Nat := 4237468805870452020335221

theorem tailTrace_8252441 : CollatzResearch.WordTrace tailWord_8252441 prefixEnd_8252441 4237468805870452020335221 := by
  unfold tailWord_8252441
  simp only [CollatzResearch.WordTrace]
  refine ⟨300991250695823136559469177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200660833797215424372979451 300991250695823136559469177)
  ·
    refine ⟨225743438021867352419601883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300991250695823136559469177 225743438021867352419601883)
    ·
      refine ⟨338615157032801028629402825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225743438021867352419601883 338615157032801028629402825)
      ·
        refine ⟨253961367774600771472052119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338615157032801028629402825 253961367774600771472052119)
        ·
          refine ⟨380942051661901157208078179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253961367774600771472052119 380942051661901157208078179)
          ·
            refine ⟨571413077492851735812117269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380942051661901157208078179 571413077492851735812117269)
            ·
              refine ⟨26784988007477425116192997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571413077492851735812117269 26784988007477425116192997)
              ·
                refine ⟨5022185251402017209286187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26784988007477425116192997 5022185251402017209286187)
                ·
                  refine ⟨7533277877103025813929281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022185251402017209286187 7533277877103025813929281)
                  ·
                    refine ⟨5649958407827269360446961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533277877103025813929281 5649958407827269360446961)
                    ·
                      refine ⟨4237468805870452020335221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5649958407827269360446961 4237468805870452020335221)
                      ·
                        rfl

theorem cell23_8252441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_8252441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252441 prefixEnd_8252441 := by exact prefixLift 8252441
  have htrace : WordTrace (prefixWord ++ tailWord_8252441) baseStart_8252441 baseEnd_8252441 := by
    simpa [prefixWord, tailWord_8252441, baseEnd_8252441] using wordTrace_append hprefix tailTrace_8252441
  have hstable : (prefixWord ++ tailWord_8252441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252441).length < 2 ^ (prefixWord ++ tailWord_8252441).sum := by decide
  have hdescent : baseEnd_8252441 < baseStart_8252441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252490 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_8252490 : Nat := 118140960795 + 8252490 * 2 ^ 59
def prefixEnd_8252490 : Nat := 4983230072969 + 3 ^ 40 * 8252490 * 2
def baseEnd_8252490 : Nat := 1412497988807507442874165

theorem tailTrace_8252490 : CollatzResearch.WordTrace tailWord_8252490 prefixEnd_8252490 1412497988807507442874165 := by
  unfold tailWord_8252490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248259468161404482000731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200662025248430411952001949 75248259468161404482000731)
  ·
    refine ⟨112872389202242106723001097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75248259468161404482000731 112872389202242106723001097)
    ·
      refine ⟨84654291901681580042250823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112872389202242106723001097 84654291901681580042250823)
      ·
        refine ⟨126981437852522370063376235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84654291901681580042250823 126981437852522370063376235)
        ·
          refine ⟨190472156778783555095064353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126981437852522370063376235 190472156778783555095064353)
          ·
            refine ⟨142854117584087666321298265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190472156778783555095064353 142854117584087666321298265)
            ·
              refine ⟨107140588188065749740973699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142854117584087666321298265 107140588188065749740973699)
              ·
                refine ⟨160710882282098624611460549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107140588188065749740973699 160710882282098624611460549)
                ·
                  refine ⟨30133290427893492114648853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160710882282098624611460549 30133290427893492114648853)
                  ·
                    refine ⟨1412497988807507442874165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30133290427893492114648853 1412497988807507442874165)
                    ·
                      rfl

theorem cell23_8252490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_8252490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252490 prefixEnd_8252490 := by exact prefixLift 8252490
  have htrace : WordTrace (prefixWord ++ tailWord_8252490) baseStart_8252490 baseEnd_8252490 := by
    simpa [prefixWord, tailWord_8252490, baseEnd_8252490] using wordTrace_append hprefix tailTrace_8252490
  have hstable : (prefixWord ++ tailWord_8252490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252490).length < 2 ^ (prefixWord ++ tailWord_8252490).sum := by decide
  have hdescent : baseEnd_8252490 < baseStart_8252490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252502 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_8252502 : Nat := 118140960795 + 8252502 * 2 ^ 59
def prefixEnd_8252502 : Nat := 4983230072969 + 3 ^ 40 * 8252502 * 2
def baseEnd_8252502 : Nat := 1412500042730125427224147

theorem tailTrace_8252502 : CollatzResearch.WordTrace tailWord_8252502 prefixEnd_8252502 1412500042730125427224147 := by
  unfold tailWord_8252502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812092221787633998589985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200662317032401429318293173 18812092221787633998589985)
  ·
    refine ⟨14109069166340725498942489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812092221787633998589985 14109069166340725498942489)
    ·
      refine ⟨10581801874755544124206867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14109069166340725498942489 10581801874755544124206867)
      ·
        refine ⟨15872702812133316186310301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581801874755544124206867 15872702812133316186310301)
        ·
          refine ⟨5952263554549993569866363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15872702812133316186310301 5952263554549993569866363)
          ·
            refine ⟨8928395331824990354799545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952263554549993569866363 8928395331824990354799545)
            ·
              refine ⟨6696296498868742766099659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8928395331824990354799545 6696296498868742766099659)
              ·
                refine ⟨10044444748303114149149489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696296498868742766099659 10044444748303114149149489)
                ·
                  refine ⟨7533333561227335611862117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044444748303114149149489 7533333561227335611862117)
                  ·
                    refine ⟨1412500042730125427224147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533333561227335611862117 1412500042730125427224147)
                    ·
                      rfl

theorem cell23_8252502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_8252502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252502 prefixEnd_8252502 := by exact prefixLift 8252502
  have htrace : WordTrace (prefixWord ++ tailWord_8252502) baseStart_8252502 baseEnd_8252502 := by
    simpa [prefixWord, tailWord_8252502, baseEnd_8252502] using wordTrace_append hprefix tailTrace_8252502
  have hstable : (prefixWord ++ tailWord_8252502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252502).length < 2 ^ (prefixWord ++ tailWord_8252502).sum := by decide
  have hdescent : baseEnd_8252502 < baseStart_8252502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252542 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8252542 : Nat := 118140960795 + 8252542 * 2 ^ 59
def prefixEnd_8252542 : Nat := 4983230072969 + 3 ^ 40 * 8252542 * 2
def baseEnd_8252542 : Nat := 4237520667416556125172257

theorem tailTrace_8252542 : CollatzResearch.WordTrace tailWord_8252542 prefixEnd_8252542 4237520667416556125172257 := by
  unfold tailWord_8252542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624366808557153851111985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200663289645638153872597253 37624366808557153851111985)
  ·
    refine ⟨28218275106417865388333989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37624366808557153851111985 28218275106417865388333989)
    ·
      refine ⟨5290926582453349760312623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28218275106417865388333989 5290926582453349760312623)
      ·
        refine ⟨7936389873680024640468935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290926582453349760312623 7936389873680024640468935)
        ·
          refine ⟨11904584810520036960703403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936389873680024640468935 11904584810520036960703403)
          ·
            refine ⟨17856877215780055441055105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904584810520036960703403 17856877215780055441055105)
            ·
              refine ⟨13392657911835041580791329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17856877215780055441055105 13392657911835041580791329)
              ·
                refine ⟨10044493433876281185593497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13392657911835041580791329 10044493433876281185593497)
                ·
                  refine ⟨7533370075407210889195123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044493433876281185593497 7533370075407210889195123)
                  ·
                    refine ⟨11300055113110816333792685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533370075407210889195123 11300055113110816333792685)
                    ·
                      refine ⟨4237520667416556125172257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300055113110816333792685 4237520667416556125172257)
                      ·
                        rfl

theorem cell23_8252542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8252542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252542 prefixEnd_8252542 := by exact prefixLift 8252542
  have htrace : WordTrace (prefixWord ++ tailWord_8252542) baseStart_8252542 baseEnd_8252542 := by
    simpa [prefixWord, tailWord_8252542, baseEnd_8252542] using wordTrace_append hprefix tailTrace_8252542
  have hstable : (prefixWord ++ tailWord_8252542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252542).length < 2 ^ (prefixWord ++ tailWord_8252542).sum := by decide
  have hdescent : baseEnd_8252542 < baseStart_8252542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252547 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3]
def baseStart_8252547 : Nat := 118140960795 + 8252547 * 2 ^ 59
def prefixEnd_8252547 : Nat := 4983230072969 + 3 ^ 40 * 8252547 * 2
def baseEnd_8252547 : Nat := 4237523234819828605609733

theorem tailTrace_8252547 : CollatzResearch.WordTrace tailWord_8252547 prefixEnd_8252547 4237523234819828605609733 := by
  unfold tailWord_8252547
  simp only [CollatzResearch.WordTrace]
  refine ⟨300995116833439116662827895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200663411222292744441885263 300995116833439116662827895)
  ·
    refine ⟨451492675250158674994241843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300995116833439116662827895 451492675250158674994241843)
    ·
      refine ⟨677239012875238012491362765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451492675250158674994241843 677239012875238012491362765)
      ·
        refine ⟨253964629828214254684261037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677239012875238012491362765 253964629828214254684261037)
        ·
          refine ⟨95236736185580345506597889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253964629828214254684261037 95236736185580345506597889)
          ·
            refine ⟨71427552139185259129948417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95236736185580345506597889 71427552139185259129948417)
            ·
              refine ⟨53570664104388944347461313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71427552139185259129948417 53570664104388944347461313)
              ·
                refine ⟨40177998078291708260595985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53570664104388944347461313 40177998078291708260595985)
                ·
                  refine ⟨30133498558718781195446989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40177998078291708260595985 30133498558718781195446989)
                  ·
                    refine ⟨11300061959519542948292621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30133498558718781195446989 11300061959519542948292621)
                    ·
                      refine ⟨4237523234819828605609733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300061959519542948292621 4237523234819828605609733)
                      ·
                        rfl

theorem cell23_8252547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_8252547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252547 prefixEnd_8252547 := by exact prefixLift 8252547
  have htrace : WordTrace (prefixWord ++ tailWord_8252547) baseStart_8252547 baseEnd_8252547 := by
    simpa [prefixWord, tailWord_8252547, baseEnd_8252547] using wordTrace_append hprefix tailTrace_8252547
  have hstable : (prefixWord ++ tailWord_8252547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252547).length < 2 ^ (prefixWord ++ tailWord_8252547).sum := by decide
  have hdescent : baseEnd_8252547 < baseStart_8252547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252548 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_8252548 : Nat := 118140960795 + 8252548 * 2 ^ 59
def prefixEnd_8252548 : Nat := 4983230072969 + 3 ^ 40 * 8252548 * 2
def baseEnd_8252548 : Nat := 4237523748300483101697229

theorem tailTrace_8252548 : CollatzResearch.WordTrace tailWord_8252548 prefixEnd_8252548 4237523748300483101697229 := by
  unfold tailWord_8252548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150497576653217746916807149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200663435537623662555742865 150497576653217746916807149)
  ·
    refine ⟨56436591244956655093802681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150497576653217746916807149 56436591244956655093802681)
    ·
      refine ⟨42327443433717491320352011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56436591244956655093802681 42327443433717491320352011)
      ·
        refine ⟨63491165150576236980528017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42327443433717491320352011 63491165150576236980528017)
        ·
          refine ⟨47618373862932177735396013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63491165150576236980528017 47618373862932177735396013)
          ·
            refine ⟨17856890198599566650773505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47618373862932177735396013 17856890198599566650773505)
            ·
              refine ⟨13392667648949674988080129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17856890198599566650773505 13392667648949674988080129)
              ·
                refine ⟨10044500736712256241060097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13392667648949674988080129 10044500736712256241060097)
                ·
                  refine ⟨7533375552534192180795073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044500736712256241060097 7533375552534192180795073)
                  ·
                    refine ⟨5650031664400644135596305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533375552534192180795073 5650031664400644135596305)
                    ·
                      refine ⟨4237523748300483101697229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650031664400644135596305 4237523748300483101697229)
                      ·
                        rfl

theorem cell23_8252548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_8252548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252548 prefixEnd_8252548 := by exact prefixLift 8252548
  have htrace : WordTrace (prefixWord ++ tailWord_8252548) baseStart_8252548 baseEnd_8252548 := by
    simpa [prefixWord, tailWord_8252548, baseEnd_8252548] using wordTrace_append hprefix tailTrace_8252548
  have hstable : (prefixWord ++ tailWord_8252548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252548).length < 2 ^ (prefixWord ++ tailWord_8252548).sum := by decide
  have hdescent : baseEnd_8252548 < baseStart_8252548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252554 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_8252554 : Nat := 118140960795 + 8252554 * 2 ^ 59
def prefixEnd_8252554 : Nat := 4983230072969 + 3 ^ 40 * 8252554 * 2
def baseEnd_8252554 : Nat := 470836314353823342024689

theorem tailTrace_8252554 : CollatzResearch.WordTrace tailWord_8252554 prefixEnd_8252554 470836314353823342024689 := by
  unfold tailWord_8252554
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248843036103439214583179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200663581429609171238888477 75248843036103439214583179)
  ·
    refine ⟨112873264554155158821874769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75248843036103439214583179 112873264554155158821874769)
    ·
      refine ⟨84654948415616369116406077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112873264554155158821874769 84654948415616369116406077)
      ·
        refine ⟨31745605655856138418652279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84654948415616369116406077 31745605655856138418652279)
        ·
          refine ⟨47618408483784207627978419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31745605655856138418652279 47618408483784207627978419)
          ·
            refine ⟨71427612725676311441967629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47618408483784207627978419 71427612725676311441967629)
            ·
              refine ⟨26785354772128616790737861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71427612725676311441967629 26785354772128616790737861)
              ·
                refine ⟨5022254019774115648263349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26785354772128616790737861 5022254019774115648263349)
                ·
                  refine ⟨470836314353823342024689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022254019774115648263349 470836314353823342024689)
                  ·
                    rfl

theorem cell23_8252554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_8252554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252554 prefixEnd_8252554 := by exact prefixLift 8252554
  have htrace : WordTrace (prefixWord ++ tailWord_8252554) baseStart_8252554 baseEnd_8252554 := by
    simpa [prefixWord, tailWord_8252554, baseEnd_8252554] using wordTrace_append hprefix tailTrace_8252554
  have hstable : (prefixWord ++ tailWord_8252554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252554).length < 2 ^ (prefixWord ++ tailWord_8252554).sum := by decide
  have hdescent : baseEnd_8252554 < baseStart_8252554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252560 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_8252560 : Nat := 118140960795 + 8252560 * 2 ^ 59
def prefixEnd_8252560 : Nat := 4983230072969 + 3 ^ 40 * 8252560 * 2
def baseEnd_8252560 : Nat := 4237529910068337054747173

theorem tailTrace_8252560 : CollatzResearch.WordTrace tailWord_8252560 prefixEnd_8252560 4237529910068337054747173 := by
  unfold tailWord_8252560
  simp only [CollatzResearch.WordTrace]
  refine ⟨150497795491196009941525567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200663727321594679922034089 150497795491196009941525567)
  ·
    refine ⟨225746693236794014912288351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150497795491196009941525567 225746693236794014912288351)
    ·
      refine ⟨338620039855191022368432527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225746693236794014912288351 338620039855191022368432527)
      ·
        refine ⟨507930059782786533552648791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338620039855191022368432527 507930059782786533552648791)
        ·
          refine ⟨761895089674179800328973187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507930059782786533552648791 761895089674179800328973187)
          ·
            refine ⟨1142842634511269700493459781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761895089674179800328973187 1142842634511269700493459781)
            ·
              refine ⟨214282993970863068842523709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1142842634511269700493459781 214282993970863068842523709)
              ·
                refine ⟨80356122739073650815946391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214282993970863068842523709 80356122739073650815946391)
                ·
                  refine ⟨120534184108610476223919587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80356122739073650815946391 120534184108610476223919587)
                  ·
                    refine ⟨180801276162915714335879381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120534184108610476223919587 180801276162915714335879381)
                    ·
                      refine ⟨4237529910068337054747173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180801276162915714335879381 4237529910068337054747173)
                      ·
                        rfl

theorem cell23_8252560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_8252560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252560 prefixEnd_8252560 := by exact prefixLift 8252560
  have htrace : WordTrace (prefixWord ++ tailWord_8252560) baseStart_8252560 baseEnd_8252560 := by
    simpa [prefixWord, tailWord_8252560, baseEnd_8252560] using wordTrace_append hprefix tailTrace_8252560
  have hstable : (prefixWord ++ tailWord_8252560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252560).length < 2 ^ (prefixWord ++ tailWord_8252560).sum := by decide
  have hdescent : baseEnd_8252560 < baseStart_8252560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252657 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_8252657 : Nat := 118140960795 + 8252657 * 2 ^ 59
def prefixEnd_8252657 : Nat := 4983230072969 + 3 ^ 40 * 8252657 * 2
def baseEnd_8252657 : Nat := 1412526572563941058411409

theorem tailTrace_8252657 : CollatzResearch.WordTrace tailWord_8252657 prefixEnd_8252657 1412526572563941058411409 := by
  unfold tailWord_8252657
  simp only [CollatzResearch.WordTrace]
  refine ⟨300999128863040605449332225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200666085908693736966221483 300999128863040605449332225)
  ·
    refine ⟨225749346647280454086999169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300999128863040605449332225 225749346647280454086999169)
    ·
      refine ⟨169312009985460340565249377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225749346647280454086999169 169312009985460340565249377)
      ·
        refine ⟨126984007489095255423937033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169312009985460340565249377 126984007489095255423937033)
        ·
          refine ⟨95238005616821441567952775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126984007489095255423937033 95238005616821441567952775)
          ·
            refine ⟨142857008425232162351929163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95238005616821441567952775 142857008425232162351929163)
            ·
              refine ⟨214285512637848243527893745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142857008425232162351929163 214285512637848243527893745)
              ·
                refine ⟨160714134478386182645920309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214285512637848243527893745 160714134478386182645920309)
                ·
                  refine ⟨15066950107348704623055029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160714134478386182645920309 15066950107348704623055029)
                  ·
                    refine ⟨1412526572563941058411409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15066950107348704623055029 1412526572563941058411409)
                    ·
                      rfl

theorem cell23_8252657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_8252657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252657 prefixEnd_8252657 := by exact prefixLift 8252657
  have htrace : WordTrace (prefixWord ++ tailWord_8252657) baseStart_8252657 baseEnd_8252657 := by
    simpa [prefixWord, tailWord_8252657, baseEnd_8252657] using wordTrace_append hprefix tailTrace_8252657
  have hstable : (prefixWord ++ tailWord_8252657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252657).length < 2 ^ (prefixWord ++ tailWord_8252657).sum := by decide
  have hdescent : baseEnd_8252657 < baseStart_8252657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252671 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_8252671 : Nat := 118140960795 + 8252671 * 2 ^ 59
def prefixEnd_8252671 : Nat := 4983230072969 + 3 ^ 40 * 8252671 * 2
def baseEnd_8252671 : Nat := 4237586906420986120459163

theorem tailTrace_8252671 : CollatzResearch.WordTrace tailWord_8252671 prefixEnd_8252671 4237586906420986120459163 := by
  unfold tailWord_8252671
  simp only [CollatzResearch.WordTrace]
  refine ⟨300999639484989885840341867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200666426323326590560227911 300999639484989885840341867)
  ·
    refine ⟨451499459227484828760512801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300999639484989885840341867 451499459227484828760512801)
    ·
      refine ⟨338624594420613621570384601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451499459227484828760512801 338624594420613621570384601)
      ·
        refine ⟨253968445815460216177788451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338624594420613621570384601 253968445815460216177788451)
        ·
          refine ⟨380952668723190324266682677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253968445815460216177788451 380952668723190324266682677)
          ·
            refine ⟨35714312692799092900001501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380952668723190324266682677 35714312692799092900001501)
            ·
              refine ⟨13392867259799659837500563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35714312692799092900001501 13392867259799659837500563)
              ·
                refine ⟨20089300889699489756250845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392867259799659837500563 20089300889699489756250845)
                ·
                  refine ⟨7533487833637308658594067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20089300889699489756250845 7533487833637308658594067)
                  ·
                    refine ⟨11300231750455962987891101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533487833637308658594067 11300231750455962987891101)
                    ·
                      refine ⟨4237586906420986120459163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300231750455962987891101 4237586906420986120459163)
                      ·
                        rfl

theorem cell23_8252671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_8252671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252671 prefixEnd_8252671 := by exact prefixLift 8252671
  have htrace : WordTrace (prefixWord ++ tailWord_8252671) baseStart_8252671 baseEnd_8252671 := by
    simpa [prefixWord, tailWord_8252671, baseEnd_8252671] using wordTrace_append hprefix tailTrace_8252671
  have hstable : (prefixWord ++ tailWord_8252671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252671).length < 2 ^ (prefixWord ++ tailWord_8252671).sum := by decide
  have hdescent : baseEnd_8252671 < baseStart_8252671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252698 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_8252698 : Nat := 118140960795 + 8252698 * 2 ^ 59
def prefixEnd_8252698 : Nat := 4983230072969 + 3 ^ 40 * 8252698 * 2
def baseEnd_8252698 : Nat := 4237600770398657514821539

theorem tailTrace_8252698 : CollatzResearch.WordTrace tailWord_8252698 prefixEnd_8252698 4237600770398657514821539 := by
  unfold tailWord_8252698
  simp only [CollatzResearch.WordTrace]
  refine ⟨75250156063973017362893687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200667082837261379634383165 75250156063973017362893687)
  ·
    refine ⟨112875234095959526044340531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75250156063973017362893687 112875234095959526044340531)
    ·
      refine ⟨169312851143939289066510797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112875234095959526044340531 169312851143939289066510797)
      ·
        refine ⟨63492319178977233399941549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169312851143939289066510797 63492319178977233399941549)
        ·
          refine ⟨23809619692116462524978081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63492319178977233399941549 23809619692116462524978081)
          ·
            refine ⟨17857214769087346893733561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23809619692116462524978081 17857214769087346893733561)
            ·
              refine ⟨13392911076815510170300171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17857214769087346893733561 13392911076815510170300171)
              ·
                refine ⟨20089366615223265255450257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392911076815510170300171 20089366615223265255450257)
                ·
                  refine ⟨15067024961417448941587693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089366615223265255450257 15067024961417448941587693)
                  ·
                    refine ⟨5650134360531543353095385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15067024961417448941587693 5650134360531543353095385)
                    ·
                      refine ⟨4237600770398657514821539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650134360531543353095385 4237600770398657514821539)
                      ·
                        rfl

theorem cell23_8252698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_8252698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252698 prefixEnd_8252698 := by exact prefixLift 8252698
  have htrace : WordTrace (prefixWord ++ tailWord_8252698) baseStart_8252698 baseEnd_8252698 := by
    simpa [prefixWord, tailWord_8252698, baseEnd_8252698] using wordTrace_append hprefix tailTrace_8252698
  have hstable : (prefixWord ++ tailWord_8252698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252698).length < 2 ^ (prefixWord ++ tailWord_8252698).sum := by decide
  have hdescent : baseEnd_8252698 < baseStart_8252698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252721 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_8252721 : Nat := 118140960795 + 8252721 * 2 ^ 59
def prefixEnd_8252721 : Nat := 4983230072969 + 3 ^ 40 * 8252721 * 2
def baseEnd_8252721 : Nat := 1412537526817903641611311

theorem tailTrace_8252721 : CollatzResearch.WordTrace tailWord_8252721 prefixEnd_8252721 1412537526817903641611311 := by
  unfold tailWord_8252721
  simp only [CollatzResearch.WordTrace]
  refine ⟨301001463134808744379662017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200667642089872496253108011 301001463134808744379662017)
  ·
    refine ⟨225751097351106558284746513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301001463134808744379662017 225751097351106558284746513)
    ·
      refine ⟨169313323013329918713559885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225751097351106558284746513 169313323013329918713559885)
      ·
        refine ⟨63492496129998719517584957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169313323013329918713559885 63492496129998719517584957)
        ·
          refine ⟨23809686048749519819094359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63492496129998719517584957 23809686048749519819094359)
          ·
            refine ⟨35714529073124279728641539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23809686048749519819094359 35714529073124279728641539)
            ·
              refine ⟨53571793609686419592962309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35714529073124279728641539 53571793609686419592962309)
              ·
                refine ⟨10044711301816203673680433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53571793609686419592962309 10044711301816203673680433)
                ·
                  refine ⟨7533533476362152755260325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10044711301816203673680433 7533533476362152755260325)
                  ·
                    refine ⟨1412537526817903641611311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533533476362152755260325 1412537526817903641611311)
                    ·
                      rfl

theorem cell23_8252721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_8252721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252721 prefixEnd_8252721 := by exact prefixLift 8252721
  have htrace : WordTrace (prefixWord ++ tailWord_8252721) baseStart_8252721 baseEnd_8252721 := by
    simpa [prefixWord, tailWord_8252721, baseEnd_8252721] using wordTrace_append hprefix tailTrace_8252721
  have hstable : (prefixWord ++ tailWord_8252721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252721).length < 2 ^ (prefixWord ++ tailWord_8252721).sum := by decide
  have hdescent : baseEnd_8252721 < baseStart_8252721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252722 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_8252722 : Nat := 118140960795 + 8252722 * 2 ^ 59
def prefixEnd_8252722 : Nat := 4983230072969 + 3 ^ 40 * 8252722 * 2
def baseEnd_8252722 : Nat := 4237613093934365420921429

theorem tailTrace_8252722 : CollatzResearch.WordTrace tailWord_8252722 prefixEnd_8252722 4237613093934365420921429 := by
  unfold tailWord_8252722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75250374901951280387612105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200667666405203414366965613 75250374901951280387612105)
  ·
    refine ⟨56437781176463460290709079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75250374901951280387612105 56437781176463460290709079)
    ·
      refine ⟨84656671764695190436063619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56437781176463460290709079 84656671764695190436063619)
      ·
        refine ⟨126985007647042785654095429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84656671764695190436063619 126985007647042785654095429)
        ·
          refine ⟨23809688933820522310142893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126985007647042785654095429 23809688933820522310142893)
          ·
            refine ⟨8928633350182695866303585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23809688933820522310142893 8928633350182695866303585)
            ·
              refine ⟨6696475012637021899727689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8928633350182695866303585 6696475012637021899727689)
              ·
                refine ⟨5022356259477766424795767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696475012637021899727689 5022356259477766424795767)
                ·
                  refine ⟨7533534389216649637193651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022356259477766424795767 7533534389216649637193651)
                  ·
                    refine ⟨11300301583824974455790477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533534389216649637193651 11300301583824974455790477)
                    ·
                      refine ⟨4237613093934365420921429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300301583824974455790477 4237613093934365420921429)
                      ·
                        rfl

theorem cell23_8252722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_8252722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252722 prefixEnd_8252722 := by exact prefixLift 8252722
  have htrace : WordTrace (prefixWord ++ tailWord_8252722) baseStart_8252722 baseEnd_8252722 := by
    simpa [prefixWord, tailWord_8252722, baseEnd_8252722] using wordTrace_append hprefix tailTrace_8252722
  have hstable : (prefixWord ++ tailWord_8252722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252722).length < 2 ^ (prefixWord ++ tailWord_8252722).sum := by decide
  have hdescent : baseEnd_8252722 < baseStart_8252722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252749 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_8252749 : Nat := 118140960795 + 8252749 * 2 ^ 59
def prefixEnd_8252749 : Nat := 4983230072969 + 3 ^ 40 * 8252749 * 2
def baseEnd_8252749 : Nat := 4237626957912036815283805

theorem tailTrace_8252749 : CollatzResearch.WordTrace tailWord_8252749 prefixEnd_8252749 4237626957912036815283805 := by
  unfold tailWord_8252749
  simp only [CollatzResearch.WordTrace]
  refine ⟨301002484378707305161681301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200668322919138203441120867 301002484378707305161681301)
  ·
    refine ⟨14109491455251904929453811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 301002484378707305161681301 14109491455251904929453811)
    ·
      refine ⟨21164237182877857394180717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109491455251904929453811 21164237182877857394180717)
      ·
        refine ⟨7936588943579196522817769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21164237182877857394180717 7936588943579196522817769)
        ·
          refine ⟨5952441707684397392113327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936588943579196522817769 5952441707684397392113327)
          ·
            refine ⟨8928662561526596088169991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952441707684397392113327 8928662561526596088169991)
            ·
              refine ⟨13392993842289894132254987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928662561526596088169991 13392993842289894132254987)
              ·
                refine ⟨20089490763434841198382481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392993842289894132254987 20089490763434841198382481)
                ·
                  refine ⟨15067118072576130898786861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089490763434841198382481 15067118072576130898786861)
                  ·
                    refine ⟨5650169277216049087045073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15067118072576130898786861 5650169277216049087045073)
                    ·
                      refine ⟨4237626957912036815283805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650169277216049087045073 4237626957912036815283805)
                      ·
                        rfl

theorem cell23_8252749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_8252749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252749 prefixEnd_8252749 := by exact prefixLift 8252749
  have htrace : WordTrace (prefixWord ++ tailWord_8252749) baseStart_8252749 baseEnd_8252749 := by
    simpa [prefixWord, tailWord_8252749, baseEnd_8252749] using wordTrace_append hprefix tailTrace_8252749
  have hstable : (prefixWord ++ tailWord_8252749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252749).length < 2 ^ (prefixWord ++ tailWord_8252749).sum := by decide
  have hdescent : baseEnd_8252749 < baseStart_8252749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252871 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 2, 5]
def baseStart_8252871 : Nat := 118140960795 + 8252871 * 2 ^ 59
def prefixEnd_8252871 : Nat := 4983230072969 + 3 ^ 40 * 8252871 * 2
def baseEnd_8252871 : Nat := 1412563200850628445986081

theorem tailTrace_8252871 : CollatzResearch.WordTrace tailWord_8252871 prefixEnd_8252871 1412563200850628445986081 := by
  unfold tailWord_8252871
  simp only [CollatzResearch.WordTrace]
  refine ⟨301006934084265319997622467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200671289389510213331748311 301006934084265319997622467)
  ·
    refine ⟨451510401126397979996433701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301006934084265319997622467 451510401126397979996433701)
    ·
      refine ⟨84658200211199621249331319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451510401126397979996433701 84658200211199621249331319)
      ·
        refine ⟨126987300316799431873996979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84658200211199621249331319 126987300316799431873996979)
        ·
          refine ⟨190480950475199147810995469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126987300316799431873996979 190480950475199147810995469)
          ·
            refine ⟨71430356428199680429123301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190480950475199147810995469 71430356428199680429123301)
            ·
              refine ⟨13393191830287440080460619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71430356428199680429123301 13393191830287440080460619)
              ·
                refine ⟨20089787745431160120690929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13393191830287440080460619 20089787745431160120690929)
                ·
                  refine ⟨15067340809073370090518197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089787745431160120690929 15067340809073370090518197)
                  ·
                    refine ⟨1412563200850628445986081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15067340809073370090518197 1412563200850628445986081)
                    ·
                      rfl

theorem cell23_8252871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_8252871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252871 prefixEnd_8252871 := by exact prefixLift 8252871
  have htrace : WordTrace (prefixWord ++ tailWord_8252871) baseStart_8252871 baseEnd_8252871 := by
    simpa [prefixWord, tailWord_8252871, baseEnd_8252871] using wordTrace_append hprefix tailTrace_8252871
  have hstable : (prefixWord ++ tailWord_8252871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252871).length < 2 ^ (prefixWord ++ tailWord_8252871).sum := by decide
  have hdescent : baseEnd_8252871 < baseStart_8252871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 4, 2]
def baseStart_8252891 : Nat := 118140960795 + 8252891 * 2 ^ 59
def prefixEnd_8252891 : Nat := 4983230072969 + 3 ^ 40 * 8252891 * 2
def baseEnd_8252891 : Nat := 4237699872164975259708151

theorem tailTrace_8252891 : CollatzResearch.WordTrace tailWord_8252891 prefixEnd_8252891 4237699872164975259708151 := by
  unfold tailWord_8252891
  simp only [CollatzResearch.WordTrace]
  refine ⟨301007663544192863413350527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200671775696128575608900351 301007663544192863413350527)
  ·
    refine ⟨451511495316289295120025791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301007663544192863413350527 451511495316289295120025791)
    ·
      refine ⟨677267242974433942680038687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451511495316289295120025791 677267242974433942680038687)
      ·
        refine ⟨1015900864461650914020058031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677267242974433942680038687 1015900864461650914020058031)
        ·
          refine ⟨1523851296692476371030087047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015900864461650914020058031 1523851296692476371030087047)
          ·
            refine ⟨2285776945038714556545130571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523851296692476371030087047 2285776945038714556545130571)
            ·
              refine ⟨3428665417558071834817695857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285776945038714556545130571 3428665417558071834817695857)
              ·
                refine ⟨2571499063168553876113271893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428665417558071834817695857 2571499063168553876113271893)
                ·
                  refine ⟨30134754646506490735702405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2571499063168553876113271893 30134754646506490735702405)
                  ·
                    refine ⟨5650266496219967012944201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30134754646506490735702405 5650266496219967012944201)
                    ·
                      refine ⟨4237699872164975259708151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650266496219967012944201 4237699872164975259708151)
                      ·
                        rfl

theorem cell23_8252891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4, 2].length) (baseStart_8252891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252891 prefixEnd_8252891 := by exact prefixLift 8252891
  have htrace : WordTrace (prefixWord ++ tailWord_8252891) baseStart_8252891 baseEnd_8252891 := by
    simpa [prefixWord, tailWord_8252891, baseEnd_8252891] using wordTrace_append hprefix tailTrace_8252891
  have hstable : (prefixWord ++ tailWord_8252891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252891).length < 2 ^ (prefixWord ++ tailWord_8252891).sum := by decide
  have hdescent : baseEnd_8252891 < baseStart_8252891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252911 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_8252911 : Nat := 118140960795 + 8252911 * 2 ^ 59
def prefixEnd_8252911 : Nat := 4983230072969 + 3 ^ 40 * 8252911 * 2
def baseEnd_8252911 : Nat := 4237710141778065181458059

theorem tailTrace_8252911 : CollatzResearch.WordTrace tailWord_8252911 prefixEnd_8252911 4237710141778065181458059 := by
  unfold tailWord_8252911
  simp only [CollatzResearch.WordTrace]
  refine ⟨301008393004120406829078587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200672262002746937886052391 301008393004120406829078587)
  ·
    refine ⟨451512589506180610243617881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301008393004120406829078587 451512589506180610243617881)
    ·
      refine ⟨338634442129635457682713411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451512589506180610243617881 338634442129635457682713411)
      ·
        refine ⟨507951663194453186524070117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338634442129635457682713411 507951663194453186524070117)
        ·
          refine ⟨95240936848959972473263147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507951663194453186524070117 95240936848959972473263147)
          ·
            refine ⟨142861405273439958709894721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95240936848959972473263147 142861405273439958709894721)
            ·
              refine ⟨107146053955079969032421041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142861405273439958709894721 107146053955079969032421041)
              ·
                refine ⟨80359540466309976774315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107146053955079969032421041 80359540466309976774315781)
                ·
                  refine ⟨15067413837433120645184209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80359540466309976774315781 15067413837433120645184209)
                  ·
                    refine ⟨11300560378074840483888157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15067413837433120645184209 11300560378074840483888157)
                    ·
                      refine ⟨4237710141778065181458059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300560378074840483888157 4237710141778065181458059)
                      ·
                        rfl

theorem cell23_8252911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_8252911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252911 prefixEnd_8252911 := by exact prefixLift 8252911
  have htrace : WordTrace (prefixWord ++ tailWord_8252911) baseStart_8252911 baseEnd_8252911 := by
    simpa [prefixWord, tailWord_8252911, baseEnd_8252911] using wordTrace_append hprefix tailTrace_8252911
  have hstable : (prefixWord ++ tailWord_8252911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252911).length < 2 ^ (prefixWord ++ tailWord_8252911).sum := by decide
  have hdescent : baseEnd_8252911 < baseStart_8252911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252918 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_8252918 : Nat := 118140960795 + 8252918 * 2 ^ 59
def prefixEnd_8252918 : Nat := 4983230072969 + 3 ^ 40 * 8252918 * 2
def baseEnd_8252918 : Nat := 1412571245380882218023509

theorem tailTrace_8252918 : CollatzResearch.WordTrace tailWord_8252918 prefixEnd_8252918 1412571245380882218023509 := by
  unfold tailWord_8252918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813040519693440439036463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200672432210063364683055605 18813040519693440439036463)
  ·
    refine ⟨28219560779540160658554695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813040519693440439036463 28219560779540160658554695)
    ·
      refine ⟨42329341169310240987832043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28219560779540160658554695 42329341169310240987832043)
      ·
        refine ⟨63494011753965361481748065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42329341169310240987832043 63494011753965361481748065)
        ·
          refine ⟨47620508815474021111311049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63494011753965361481748065 47620508815474021111311049)
          ·
            refine ⟨35715381611605515833483287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47620508815474021111311049 35715381611605515833483287)
            ·
              refine ⟨53573072417408273750224931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35715381611605515833483287 53573072417408273750224931)
              ·
                refine ⟨80359608626112410625337397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53573072417408273750224931 80359608626112410625337397)
                ·
                  refine ⟨7533713308698038496125381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80359608626112410625337397 7533713308698038496125381)
                  ·
                    refine ⟨1412571245380882218023509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533713308698038496125381 1412571245380882218023509)
                    ·
                      rfl

theorem cell23_8252918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_8252918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252918 prefixEnd_8252918 := by exact prefixLift 8252918
  have htrace : WordTrace (prefixWord ++ tailWord_8252918) baseStart_8252918 baseEnd_8252918 := by
    simpa [prefixWord, tailWord_8252918, baseEnd_8252918] using wordTrace_append hprefix tailTrace_8252918
  have hstable : (prefixWord ++ tailWord_8252918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252918).length < 2 ^ (prefixWord ++ tailWord_8252918).sum := by decide
  have hdescent : baseEnd_8252918 < baseStart_8252918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8252935 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 1, 4]
def baseStart_8252935 : Nat := 118140960795 + 8252935 * 2 ^ 59
def prefixEnd_8252935 : Nat := 4983230072969 + 3 ^ 40 * 8252935 * 2
def baseEnd_8252935 : Nat := 1412574155104591029185983

theorem tailTrace_8252935 : CollatzResearch.WordTrace tailWord_8252935 prefixEnd_8252935 1412574155104591029185983 := by
  unfold tailWord_8252935
  simp only [CollatzResearch.WordTrace]
  refine ⟨301009268356033458927952259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200672845570688972618634839 301009268356033458927952259)
  ·
    refine ⟨451513902534050188391928389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301009268356033458927952259 451513902534050188391928389)
    ·
      refine ⟨84658856725134410323486573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451513902534050188391928389 84658856725134410323486573)
      ·
        refine ⟨31747071271925403871307465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84658856725134410323486573 31747071271925403871307465)
        ·
          refine ⟨23810303453944052903480599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31747071271925403871307465 23810303453944052903480599)
          ·
            refine ⟨35715455180916079355220899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23810303453944052903480599 35715455180916079355220899)
            ·
              refine ⟨53573182771374119032831349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35715455180916079355220899 53573182771374119032831349)
              ·
                refine ⟨5022485884816323659327939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53573182771374119032831349 5022485884816323659327939)
                ·
                  refine ⟨7533728827224485488991909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022485884816323659327939 7533728827224485488991909)
                  ·
                    refine ⟨1412574155104591029185983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533728827224485488991909 1412574155104591029185983)
                    ·
                      rfl

theorem cell23_8252935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_8252935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8252935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8252935 prefixEnd_8252935 := by exact prefixLift 8252935
  have htrace : WordTrace (prefixWord ++ tailWord_8252935) baseStart_8252935 baseEnd_8252935 := by
    simpa [prefixWord, tailWord_8252935, baseEnd_8252935] using wordTrace_append hprefix tailTrace_8252935
  have hstable : (prefixWord ++ tailWord_8252935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8252935).length < 2 ^ (prefixWord ++ tailWord_8252935).sum := by decide
  have hdescent : baseEnd_8252935 < baseStart_8252935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8252935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253008 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_8253008 : Nat := 118140960795 + 8253008 * 2 ^ 59
def prefixEnd_8253008 : Nat := 4983230072969 + 3 ^ 40 * 8253008 * 2
def baseEnd_8253008 : Nat := 1412586649800517100648371

theorem tailTrace_8253008 : CollatzResearch.WordTrace tailWord_8253008 prefixEnd_8253008 1412586649800517100648371 := by
  unfold tailWord_8253008
  simp only [CollatzResearch.WordTrace]
  refine ⟨150505965442384496197679839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200674620589845994930239785 150505965442384496197679839)
  ·
    refine ⟨225758948163576744296519759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150505965442384496197679839 225758948163576744296519759)
    ·
      refine ⟨338638422245365116444779639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225758948163576744296519759 338638422245365116444779639)
      ·
        refine ⟨507957633368047674667169459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338638422245365116444779639 507957633368047674667169459)
        ·
          refine ⟨761936450052071512000754189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507957633368047674667169459 761936450052071512000754189)
          ·
            refine ⟨285726168769526817000282821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761936450052071512000754189 285726168769526817000282821)
            ·
              refine ⟨53573656644286278187553029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285726168769526817000282821 53573656644286278187553029)
              ·
                refine ⟨10045060620803677160166193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53573656644286278187553029 10045060620803677160166193)
                ·
                  refine ⟨7533795465602757870124645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10045060620803677160166193 7533795465602757870124645)
                  ·
                    refine ⟨1412586649800517100648371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533795465602757870124645 1412586649800517100648371)
                    ·
                      rfl

theorem cell23_8253008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_8253008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253008 prefixEnd_8253008 := by exact prefixLift 8253008
  have htrace : WordTrace (prefixWord ++ tailWord_8253008) baseStart_8253008 baseEnd_8253008 := by
    simpa [prefixWord, tailWord_8253008, baseEnd_8253008] using wordTrace_append hprefix tailTrace_8253008
  have hstable : (prefixWord ++ tailWord_8253008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253008).length < 2 ^ (prefixWord ++ tailWord_8253008).sum := by decide
  have hdescent : baseEnd_8253008 < baseStart_8253008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253032 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_8253032 : Nat := 118140960795 + 8253032 * 2 ^ 59
def prefixEnd_8253032 : Nat := 4983230072969 + 3 ^ 40 * 8253032 * 2
def baseEnd_8253032 : Nat := 4237772272937259208045003

theorem tailTrace_8253032 : CollatzResearch.WordTrace tailWord_8253032 prefixEnd_8253032 4237772272937259208045003 := by
  unfold tailWord_8253032
  simp only [CollatzResearch.WordTrace]
  refine ⟨150506403118341022247116675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200675204157788029662822233 150506403118341022247116675)
  ·
    refine ⟨225759604677511533370675013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150506403118341022247116675 225759604677511533370675013)
    ·
      refine ⟨42329925877033412507001565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225759604677511533370675013 42329925877033412507001565)
      ·
        refine ⟨15873722203887529690125587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42329925877033412507001565 15873722203887529690125587)
        ·
          refine ⟨23810583305831294535188381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873722203887529690125587 23810583305831294535188381)
          ·
            refine ⟨8928968739686735450695643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23810583305831294535188381 8928968739686735450695643)
            ·
              refine ⟨13393453109530103176043465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928968739686735450695643 13393453109530103176043465)
              ·
                refine ⟨10045089832147577382032599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13393453109530103176043465 10045089832147577382032599)
                ·
                  refine ⟨15067634748221366073048899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10045089832147577382032599 15067634748221366073048899)
                  ·
                    refine ⟨22601452122332049109573349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15067634748221366073048899 22601452122332049109573349)
                    ·
                      refine ⟨4237772272937259208045003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22601452122332049109573349 4237772272937259208045003)
                      ·
                        rfl

theorem cell23_8253032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_8253032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253032 prefixEnd_8253032 := by exact prefixLift 8253032
  have htrace : WordTrace (prefixWord ++ tailWord_8253032) baseStart_8253032 baseEnd_8253032 := by
    simpa [prefixWord, tailWord_8253032, baseEnd_8253032] using wordTrace_append hprefix tailTrace_8253032
  have hstable : (prefixWord ++ tailWord_8253032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253032).length < 2 ^ (prefixWord ++ tailWord_8253032).sum := by decide
  have hdescent : baseEnd_8253032 < baseStart_8253032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253045 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8253045 : Nat := 118140960795 + 8253045 * 2 ^ 59
def prefixEnd_8253045 : Nat := 4983230072969 + 3 ^ 40 * 8253045 * 2
def baseEnd_8253045 : Nat := 4237778948185767657182443

theorem tailTrace_8253045 : CollatzResearch.WordTrace tailWord_8253045 prefixEnd_8253045 4237778948185767657182443 := by
  unfold tailWord_8253045
  simp only [CollatzResearch.WordTrace]
  refine ⟨301013280385634947714456589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200675520257089965142971059 301013280385634947714456589)
  ·
    refine ⟨112879980144613105392921221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301013280385634947714456589 112879980144613105392921221)
    ·
      refine ⟨21164996277114957261172729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112879980144613105392921221 21164996277114957261172729)
      ·
        refine ⟨15873747207836217945879547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164996277114957261172729 15873747207836217945879547)
        ·
          refine ⟨23810620811754326918819321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873747207836217945879547 23810620811754326918819321)
          ·
            refine ⟨17857965608815745189114491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23810620811754326918819321 17857965608815745189114491)
            ·
              refine ⟨26786948413223617783671737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17857965608815745189114491 26786948413223617783671737)
              ·
                refine ⟨20090211309917713337753803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26786948413223617783671737 20090211309917713337753803)
                ·
                  refine ⟨30135316964876570006630705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20090211309917713337753803 30135316964876570006630705)
                  ·
                    refine ⟨22601487723657427504973029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30135316964876570006630705 22601487723657427504973029)
                    ·
                      refine ⟨4237778948185767657182443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22601487723657427504973029 4237778948185767657182443)
                      ·
                        rfl

theorem cell23_8253045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8253045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253045 prefixEnd_8253045 := by exact prefixLift 8253045
  have htrace : WordTrace (prefixWord ++ tailWord_8253045) baseStart_8253045 baseEnd_8253045 := by
    simpa [prefixWord, tailWord_8253045, baseEnd_8253045] using wordTrace_append hprefix tailTrace_8253045
  have hstable : (prefixWord ++ tailWord_8253045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253045).length < 2 ^ (prefixWord ++ tailWord_8253045).sum := by decide
  have hdescent : baseEnd_8253045 < baseStart_8253045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253065 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_8253065 : Nat := 118140960795 + 8253065 * 2 ^ 59
def prefixEnd_8253065 : Nat := 4983230072969 + 3 ^ 40 * 8253065 * 2
def baseEnd_8253065 : Nat := 4237789217798857578932351

theorem tailTrace_8253065 : CollatzResearch.WordTrace tailWord_8253065 prefixEnd_8253065 4237789217798857578932351 := by
  unfold tailWord_8253065
  simp only [CollatzResearch.WordTrace]
  refine ⟨301014009845562491130184649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200676006563708327420123099 301014009845562491130184649)
  ·
    refine ⟨225760507384171868347638487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301014009845562491130184649 225760507384171868347638487)
    ·
      refine ⟨338640761076257802521457731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225760507384171868347638487 338640761076257802521457731)
      ·
        refine ⟨507961141614386703782186597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338640761076257802521457731 507961141614386703782186597)
        ·
          refine ⟨95242714052697506959159987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507961141614386703782186597 95242714052697506959159987)
          ·
            refine ⟨142864071079046260438739981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95242714052697506959159987 142864071079046260438739981)
            ·
              refine ⟨53574026654642347664527493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142864071079046260438739981 53574026654642347664527493)
              ·
                refine ⟨10045129997745440187098905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53574026654642347664527493 10045129997745440187098905)
                ·
                  refine ⟨7533847498309080140324179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10045129997745440187098905 7533847498309080140324179)
                  ·
                    refine ⟨11300771247463620210486269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533847498309080140324179 11300771247463620210486269)
                    ·
                      refine ⟨4237789217798857578932351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11300771247463620210486269 4237789217798857578932351)
                      ·
                        rfl

theorem cell23_8253065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_8253065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253065 prefixEnd_8253065 := by exact prefixLift 8253065
  have htrace : WordTrace (prefixWord ++ tailWord_8253065) baseStart_8253065 baseEnd_8253065 := by
    simpa [prefixWord, tailWord_8253065, baseEnd_8253065] using wordTrace_append hprefix tailTrace_8253065
  have hstable : (prefixWord ++ tailWord_8253065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253065).length < 2 ^ (prefixWord ++ tailWord_8253065).sum := by decide
  have hdescent : baseEnd_8253065 < baseStart_8253065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253066 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_8253066 : Nat := 118140960795 + 8253066 * 2 ^ 59
def prefixEnd_8253066 : Nat := 4983230072969 + 3 ^ 40 * 8253066 * 2
def baseEnd_8253066 : Nat := 4237789731279512075019847

theorem tailTrace_8253066 : CollatzResearch.WordTrace tailWord_8253066 prefixEnd_8253066 4237789731279512075019847 := by
  unfold tailWord_8253066
  simp only [CollatzResearch.WordTrace]
  refine ⟨75253511579639717075242763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200676030879039245533980701 75253511579639717075242763)
  ·
    refine ⟨112880267369459575612864145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75253511579639717075242763 112880267369459575612864145)
    ·
      refine ⟨84660200527094681709648109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112880267369459575612864145 84660200527094681709648109)
      ·
        refine ⟨31747575197660505641118041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84660200527094681709648109 31747575197660505641118041)
        ·
          refine ⟨23810681398245379230838531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31747575197660505641118041 23810681398245379230838531)
          ·
            refine ⟨35716022097368068846257797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23810681398245379230838531 35716022097368068846257797)
            ·
              refine ⟨6696754143256512908673337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35716022097368068846257797 6696754143256512908673337)
              ·
                refine ⟨5022565607442384681505003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696754143256512908673337 5022565607442384681505003)
                ·
                  refine ⟨7533848411163577022257505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022565607442384681505003 7533848411163577022257505)
                  ·
                    refine ⟨5650386308372682766693129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7533848411163577022257505 5650386308372682766693129)
                    ·
                      refine ⟨4237789731279512075019847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650386308372682766693129 4237789731279512075019847)
                      ·
                        rfl

theorem cell23_8253066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_8253066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253066 prefixEnd_8253066 := by exact prefixLift 8253066
  have htrace : WordTrace (prefixWord ++ tailWord_8253066) baseStart_8253066 baseEnd_8253066 := by
    simpa [prefixWord, tailWord_8253066, baseEnd_8253066] using wordTrace_append hprefix tailTrace_8253066
  have hstable : (prefixWord ++ tailWord_8253066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253066).length < 2 ^ (prefixWord ++ tailWord_8253066).sum := by decide
  have hdescent : baseEnd_8253066 < baseStart_8253066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253109 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_8253109 : Nat := 118140960795 + 8253109 * 2 ^ 59
def prefixEnd_8253109 : Nat := 4983230072969 + 3 ^ 40 * 8253109 * 2
def baseEnd_8253109 : Nat := 4237811810947655406782149

theorem tailTrace_8253109 : CollatzResearch.WordTrace tailWord_8253109 prefixEnd_8253109 4237811810947655406782149 := by
  unfold tailWord_8253109
  simp only [CollatzResearch.WordTrace]
  refine ⟨301015614657403086644786381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200677076438268724429857587 301015614657403086644786381)
  ·
    refine ⟨112880855496526157491794893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301015614657403086644786381 112880855496526157491794893)
    ·
      refine ⟨42330320811197309059423085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112880855496526157491794893 42330320811197309059423085)
      ·
        refine ⟨15873870304198990897283657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42330320811197309059423085 15873870304198990897283657)
        ·
          refine ⟨11905402728149243172962743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15873870304198990897283657 11905402728149243172962743)
          ·
            refine ⟨17858104092223864759444115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905402728149243172962743 17858104092223864759444115)
            ·
              refine ⟨26787156138335797139166173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17858104092223864759444115 26787156138335797139166173)
              ·
                refine ⟨10045183551875923927187315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26787156138335797139166173 10045183551875923927187315)
                ·
                  refine ⟨15067775327813885890780973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10045183551875923927187315 15067775327813885890780973)
                  ·
                    refine ⟨5650415747930207209042865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15067775327813885890780973 5650415747930207209042865)
                    ·
                      refine ⟨4237811810947655406782149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650415747930207209042865 4237811810947655406782149)
                      ·
                        rfl

theorem cell23_8253109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_8253109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253109 prefixEnd_8253109 := by exact prefixLift 8253109
  have htrace : WordTrace (prefixWord ++ tailWord_8253109) baseStart_8253109 baseEnd_8253109 := by
    simpa [prefixWord, tailWord_8253109, baseEnd_8253109] using wordTrace_append hprefix tailTrace_8253109
  have hstable : (prefixWord ++ tailWord_8253109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253109).length < 2 ^ (prefixWord ++ tailWord_8253109).sum := by decide
  have hdescent : baseEnd_8253109 < baseStart_8253109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253128 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 7]
def baseStart_8253128 : Nat := 118140960795 + 8253128 * 2 ^ 59
def prefixEnd_8253128 : Nat := 4983230072969 + 3 ^ 40 * 8253128 * 2
def baseEnd_8253128 : Nat := 470869063008898981382729

theorem tailTrace_8253128 : CollatzResearch.WordTrace tailWord_8253128 prefixEnd_8253128 470869063008898981382729 := by
  unfold tailWord_8253128
  simp only [CollatzResearch.WordTrace]
  refine ⟨150508153822167126444864019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200677538429556168593152025 150508153822167126444864019)
  ·
    refine ⟨225762230733250689667296029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150508153822167126444864019 225762230733250689667296029)
    ·
      refine ⟨84660836524969008625236011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225762230733250689667296029 84660836524969008625236011)
      ·
        refine ⟨126991254787453512937854017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84660836524969008625236011 126991254787453512937854017)
        ·
          refine ⟨95243441090590134703390513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126991254787453512937854017 95243441090590134703390513)
          ·
            refine ⟨71432580817942601027542885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95243441090590134703390513 71432580817942601027542885)
            ·
              refine ⟨13393608903364237692664291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71432580817942601027542885 13393608903364237692664291)
              ·
                refine ⟨20090413355046356538996437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13393608903364237692664291 20090413355046356538996437)
                ·
                  refine ⟨470869063008898981382729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20090413355046356538996437 470869063008898981382729)
                  ·
                    rfl

theorem cell23_8253128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_8253128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253128 prefixEnd_8253128 := by exact prefixLift 8253128
  have htrace : WordTrace (prefixWord ++ tailWord_8253128) baseStart_8253128 baseEnd_8253128 := by
    simpa [prefixWord, tailWord_8253128, baseEnd_8253128] using wordTrace_append hprefix tailTrace_8253128
  have hstable : (prefixWord ++ tailWord_8253128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253128).length < 2 ^ (prefixWord ++ tailWord_8253128).sum := by decide
  have hdescent : baseEnd_8253128 < baseStart_8253128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253195 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 4, 2]
def baseStart_8253195 : Nat := 118140960795 + 8253195 * 2 ^ 59
def prefixEnd_8253195 : Nat := 4983230072969 + 3 ^ 40 * 8253195 * 2
def baseEnd_8253195 : Nat := 4237855970283942070306753

theorem tailTrace_8253195 : CollatzResearch.WordTrace tailWord_8253195 prefixEnd_8253195 4237855970283942070306753 := by
  unfold tailWord_8253195
  simp only [CollatzResearch.WordTrace]
  refine ⟨301018751335091523332417039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200679167556727682221611359 301018751335091523332417039)
  ·
    refine ⟨451528127002637284998625559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301018751335091523332417039 451528127002637284998625559)
    ·
      refine ⟨677292190503955927497938339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451528127002637284998625559 677292190503955927497938339)
      ·
        refine ⟨1015938285755933891246907509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677292190503955927497938339 1015938285755933891246907509)
        ·
          refine ⟨95244214289618802304397579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1015938285755933891246907509 95244214289618802304397579)
          ·
            refine ⟨142866321434428203456596369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95244214289618802304397579 142866321434428203456596369)
            ·
              refine ⟨107149741075821152592447277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142866321434428203456596369 107149741075821152592447277)
              ·
                refine ⟨40181152903432932222167729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107149741075821152592447277 40181152903432932222167729)
                ·
                  refine ⟨30135864677574699166625797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40181152903432932222167729 30135864677574699166625797)
                  ·
                    refine ⟨5650474627045256093742337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30135864677574699166625797 5650474627045256093742337)
                    ·
                      refine ⟨4237855970283942070306753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650474627045256093742337 4237855970283942070306753)
                      ·
                        rfl

theorem cell23_8253195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4, 2].length) (baseStart_8253195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253195 prefixEnd_8253195 := by exact prefixLift 8253195
  have htrace : WordTrace (prefixWord ++ tailWord_8253195) baseStart_8253195 baseEnd_8253195 := by
    simpa [prefixWord, tailWord_8253195, baseEnd_8253195] using wordTrace_append hprefix tailTrace_8253195
  have hstable : (prefixWord ++ tailWord_8253195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253195).length < 2 ^ (prefixWord ++ tailWord_8253195).sum := by decide
  have hdescent : baseEnd_8253195 < baseStart_8253195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253208 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_8253208 : Nat := 118140960795 + 8253208 * 2 ^ 59
def prefixEnd_8253208 : Nat := 4983230072969 + 3 ^ 40 * 8253208 * 2
def baseEnd_8253208 : Nat := 4237862645532450519444193

theorem tailTrace_8253208 : CollatzResearch.WordTrace tailWord_8253208 prefixEnd_8253208 4237862645532450519444193 := by
  unfold tailWord_8253208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150509612742022213276320139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200679483656029617701760185 150509612742022213276320139)
  ·
    refine ⟨225764419113033319914480209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150509612742022213276320139 225764419113033319914480209)
    ·
      refine ⟨169323314334774989935860157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225764419113033319914480209 169323314334774989935860157)
      ·
        refine ⟨63496242875540621225947559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169323314334774989935860157 63496242875540621225947559)
        ·
          refine ⟨95244364313310931838921339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63496242875540621225947559 95244364313310931838921339)
          ·
            refine ⟨142866546469966397758382009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95244364313310931838921339 142866546469966397758382009)
            ·
              refine ⟨107149909852474798318786507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142866546469966397758382009 107149909852474798318786507)
              ·
                refine ⟨160724864778712197478179761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107149909852474798318786507 160724864778712197478179761)
                ·
                  refine ⟨120543648584034148108634821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160724864778712197478179761 120543648584034148108634821)
                  ·
                    refine ⟨22601934109506402770369029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120543648584034148108634821 22601934109506402770369029)
                    ·
                      refine ⟨4237862645532450519444193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22601934109506402770369029 4237862645532450519444193)
                      ·
                        rfl

theorem cell23_8253208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_8253208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253208 prefixEnd_8253208 := by exact prefixLift 8253208
  have htrace : WordTrace (prefixWord ++ tailWord_8253208) baseStart_8253208 baseEnd_8253208 := by
    simpa [prefixWord, tailWord_8253208, baseEnd_8253208] using wordTrace_append hprefix tailTrace_8253208
  have hstable : (prefixWord ++ tailWord_8253208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253208).length < 2 ^ (prefixWord ++ tailWord_8253208).sum := by decide
  have hdescent : baseEnd_8253208 < baseStart_8253208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253258 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_8253258 : Nat := 118140960795 + 8253258 * 2 ^ 59
def prefixEnd_8253258 : Nat := 4983230072969 + 3 ^ 40 * 8253258 * 2
def baseEnd_8253258 : Nat := 4237888319565175323818963

theorem tailTrace_8253258 : CollatzResearch.WordTrace tailWord_8253258 prefixEnd_8253258 4237888319565175323818963 := by
  unfold tailWord_8253258
  simp only [CollatzResearch.WordTrace]
  refine ⟨75255262283465821272990107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200680699422575523394640285 75255262283465821272990107)
  ·
    refine ⟨112882893425198731909485161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75255262283465821272990107 112882893425198731909485161)
    ·
      refine ⟨84662170068899048932113871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112882893425198731909485161 84662170068899048932113871)
      ·
        refine ⟨126993255103348573398170807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84662170068899048932113871 126993255103348573398170807)
        ·
          refine ⟨190489882655022860097256211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126993255103348573398170807 190489882655022860097256211)
          ·
            refine ⟨285734823982534290145884317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190489882655022860097256211 285734823982534290145884317)
            ·
              refine ⟨107150558993450358804706619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285734823982534290145884317 107150558993450358804706619)
              ·
                refine ⟨160725838490175538207059929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107150558993450358804706619 160725838490175538207059929)
                ·
                  refine ⟨120544378867631653655294947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160725838490175538207059929 120544378867631653655294947)
                  ·
                    refine ⟨180816568301447480482942421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120544378867631653655294947 180816568301447480482942421)
                    ·
                      refine ⟨4237888319565175323818963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180816568301447480482942421 4237888319565175323818963)
                      ·
                        rfl

theorem cell23_8253258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_8253258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253258 prefixEnd_8253258 := by exact prefixLift 8253258
  have htrace : WordTrace (prefixWord ++ tailWord_8253258) baseStart_8253258 baseEnd_8253258 := by
    simpa [prefixWord, tailWord_8253258, baseEnd_8253258] using wordTrace_append hprefix tailTrace_8253258
  have hstable : (prefixWord ++ tailWord_8253258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253258).length < 2 ^ (prefixWord ++ tailWord_8253258).sum := by decide
  have hdescent : baseEnd_8253258 < baseStart_8253258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253265 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_8253265 : Nat := 118140960795 + 8253265 * 2 ^ 59
def prefixEnd_8253265 : Nat := 4983230072969 + 3 ^ 40 * 8253265 * 2
def baseEnd_8253265 : Nat := 1412630637976585598810477

theorem tailTrace_8253265 : CollatzResearch.WordTrace tailWord_8253265 prefixEnd_8253265 1412630637976585598810477 := by
  unfold tailWord_8253265
  simp only [CollatzResearch.WordTrace]
  refine ⟨301021304444837925287465249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200680869629891950191643499 301021304444837925287465249)
  ·
    refine ⟨225765978333628443965598937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301021304444837925287465249 225765978333628443965598937)
    ·
      refine ⟨169324483750221332974199203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225765978333628443965598937 169324483750221332974199203)
      ·
        refine ⟨253986725625331999461298805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169324483750221332974199203 253986725625331999461298805)
        ·
          refine ⟨23811255527374874949496763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253986725625331999461298805 23811255527374874949496763)
          ·
            refine ⟨35716883291062312424245145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23811255527374874949496763 35716883291062312424245145)
            ·
              refine ⟨26787662468296734318183859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35716883291062312424245145 26787662468296734318183859)
              ·
                refine ⟨40181493702445101477275789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26787662468296734318183859 40181493702445101477275789)
                ·
                  refine ⟨15068060138416913053978421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40181493702445101477275789 15068060138416913053978421)
                  ·
                    refine ⟨1412630637976585598810477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15068060138416913053978421 1412630637976585598810477)
                    ·
                      rfl

theorem cell23_8253265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_8253265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253265 prefixEnd_8253265 := by exact prefixLift 8253265
  have htrace : WordTrace (prefixWord ++ tailWord_8253265) baseStart_8253265 baseEnd_8253265 := by
    simpa [prefixWord, tailWord_8253265, baseEnd_8253265] using wordTrace_append hprefix tailTrace_8253265
  have hstable : (prefixWord ++ tailWord_8253265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253265).length < 2 ^ (prefixWord ++ tailWord_8253265).sum := by decide
  have hdescent : baseEnd_8253265 < baseStart_8253265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253279 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 3]
def baseStart_8253279 : Nat := 118140960795 + 8253279 * 2 ^ 59
def prefixEnd_8253279 : Nat := 4983230072969 + 3 ^ 40 * 8253279 * 2
def baseEnd_8253279 : Nat := 4237899102658919741656367

theorem tailTrace_8253279 : CollatzResearch.WordTrace tailWord_8253279 prefixEnd_8253279 4237899102658919741656367 := by
  unfold tailWord_8253279
  simp only [CollatzResearch.WordTrace]
  refine ⟨301021815066787205678474891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200681210044524803785649927 301021815066787205678474891)
  ·
    refine ⟨451532722600180808517712337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301021815066787205678474891 451532722600180808517712337)
    ·
      refine ⟨338649541950135606388284253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451532722600180808517712337 338649541950135606388284253)
      ·
        refine ⟨126993578231300852395606595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338649541950135606388284253 126993578231300852395606595)
        ·
          refine ⟨190490367346951278593409893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126993578231300852395606595 190490367346951278593409893)
          ·
            refine ⟨35716943877553364736264355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190490367346951278593409893 35716943877553364736264355)
            ·
              refine ⟨53575415816330047104396533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35716943877553364736264355 53575415816330047104396533)
              ·
                refine ⟨5022695232780941916037175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53575415816330047104396533 5022695232780941916037175)
                ·
                  refine ⟨7534042849171412874055763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022695232780941916037175 7534042849171412874055763)
                  ·
                    refine ⟨11301064273757119311083645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534042849171412874055763 11301064273757119311083645)
                    ·
                      refine ⟨4237899102658919741656367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11301064273757119311083645 4237899102658919741656367)
                      ·
                        rfl

theorem cell23_8253279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_8253279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253279 prefixEnd_8253279 := by exact prefixLift 8253279
  have htrace : WordTrace (prefixWord ++ tailWord_8253279) baseStart_8253279 baseEnd_8253279 := by
    simpa [prefixWord, tailWord_8253279, baseEnd_8253279] using wordTrace_append hprefix tailTrace_8253279
  have hstable : (prefixWord ++ tailWord_8253279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253279).length < 2 ^ (prefixWord ++ tailWord_8253279).sum := by decide
  have hdescent : baseEnd_8253279 < baseStart_8253279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253305 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_8253305 : Nat := 118140960795 + 8253305 * 2 ^ 59
def prefixEnd_8253305 : Nat := 4983230072969 + 3 ^ 40 * 8253305 * 2
def baseEnd_8253305 : Nat := 4237912453155936639931247

theorem tailTrace_8253305 : CollatzResearch.WordTrace tailWord_8253305 prefixEnd_8253305 4237912453155936639931247 := by
  unfold tailWord_8253305
  simp only [CollatzResearch.WordTrace]
  refine ⟨301022763364693012118921369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200681842243128674745947579 301022763364693012118921369)
  ·
    refine ⟨225767072523519759089191027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301022763364693012118921369 225767072523519759089191027)
    ·
      refine ⟨338650608785279638633786541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225767072523519759089191027 338650608785279638633786541)
      ·
        refine ⟨126993978294479864487669953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338650608785279638633786541 126993978294479864487669953)
        ·
          refine ⟨95245483720859898365752465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126993978294479864487669953 95245483720859898365752465)
          ·
            refine ⟨71434112790644923774314349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95245483720859898365752465 71434112790644923774314349)
            ·
              refine ⟨26787792296491846415367881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71434112790644923774314349 26787792296491846415367881)
              ·
                refine ⟨20090844222368884811525911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26787792296491846415367881 20090844222368884811525911)
                ·
                  refine ⟨30136266333553327217288867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20090844222368884811525911 30136266333553327217288867)
                  ·
                    refine ⟨45204399500329990825933301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30136266333553327217288867 45204399500329990825933301)
                    ·
                      refine ⟨4237912453155936639931247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45204399500329990825933301 4237912453155936639931247)
                      ·
                        rfl

theorem cell23_8253305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_8253305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253305 prefixEnd_8253305 := by exact prefixLift 8253305
  have htrace : WordTrace (prefixWord ++ tailWord_8253305) baseStart_8253305 baseEnd_8253305 := by
    simpa [prefixWord, tailWord_8253305, baseEnd_8253305] using wordTrace_append hprefix tailTrace_8253305
  have hstable : (prefixWord ++ tailWord_8253305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253305).length < 2 ^ (prefixWord ++ tailWord_8253305).sum := by decide
  have hdescent : baseEnd_8253305 < baseStart_8253305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253315 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_8253315 : Nat := 118140960795 + 8253315 * 2 ^ 59
def prefixEnd_8253315 : Nat := 4983230072969 + 3 ^ 40 * 8253315 * 2
def baseEnd_8253315 : Nat := 4237917587962481600806201

theorem tailTrace_8253315 : CollatzResearch.WordTrace tailWord_8253315 prefixEnd_8253315 4237917587962481600806201 := by
  unfold tailWord_8253315
  simp only [CollatzResearch.WordTrace]
  refine ⟨301023128094656783826785399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200682085396437855884523599 301023128094656783826785399)
  ·
    refine ⟨451534692141985175740178099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301023128094656783826785399 451534692141985175740178099)
    ·
      refine ⟨677302038212977763610267149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451534692141985175740178099 677302038212977763610267149)
      ·
        refine ⟨253988264329866661353850181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677302038212977763610267149 253988264329866661353850181)
        ·
          refine ⟨47622799561849999003846909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253988264329866661353850181 47622799561849999003846909)
          ·
            refine ⟨17858549835693749626442591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47622799561849999003846909 17858549835693749626442591)
            ·
              refine ⟨26787824753540624439663887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17858549835693749626442591 26787824753540624439663887)
              ·
                refine ⟨40181737130310936659495831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26787824753540624439663887 40181737130310936659495831)
                ·
                  refine ⟨60272605695466404989243747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40181737130310936659495831 60272605695466404989243747)
                  ·
                    refine ⟨90408908543199607483865621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60272605695466404989243747 90408908543199607483865621)
                    ·
                      refine ⟨4237917587962481600806201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90408908543199607483865621 4237917587962481600806201)
                      ·
                        rfl

theorem cell23_8253315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_8253315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253315 prefixEnd_8253315 := by exact prefixLift 8253315
  have htrace : WordTrace (prefixWord ++ tailWord_8253315) baseStart_8253315 baseEnd_8253315 := by
    simpa [prefixWord, tailWord_8253315, baseEnd_8253315] using wordTrace_append hprefix tailTrace_8253315
  have hstable : (prefixWord ++ tailWord_8253315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253315).length < 2 ^ (prefixWord ++ tailWord_8253315).sum := by decide
  have hdescent : baseEnd_8253315 < baseStart_8253315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253319 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_8253319 : Nat := 118140960795 + 8253319 * 2 ^ 59
def prefixEnd_8253319 : Nat := 4983230072969 + 3 ^ 40 * 8253319 * 2
def baseEnd_8253319 : Nat := 4237919641885099585156183

theorem tailTrace_8253319 : CollatzResearch.WordTrace tailWord_8253319 prefixEnd_8253319 4237919641885099585156183 := by
  unfold tailWord_8253319
  simp only [CollatzResearch.WordTrace]
  refine ⟨301023273986642292509931011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200682182657761528339954007 301023273986642292509931011)
  ·
    refine ⟨451534910979963438764896517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301023273986642292509931011 451534910979963438764896517)
    ·
      refine ⟨84662795808743144768418097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451534910979963438764896517 84662795808743144768418097)
      ·
        refine ⟨63497096856557358576313573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84662795808743144768418097 63497096856557358576313573)
        ·
          refine ⟨11905705660604504733058795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63497096856557358576313573 11905705660604504733058795)
          ·
            refine ⟨17858558490906757099588193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905705660604504733058795 17858558490906757099588193)
            ·
              refine ⟨13393918868180067824691145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17858558490906757099588193 13393918868180067824691145)
              ·
                refine ⟨10045439151135050868518359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13393918868180067824691145 10045439151135050868518359)
                ·
                  refine ⟨15068158726702576302777539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10045439151135050868518359 15068158726702576302777539)
                  ·
                    refine ⟨22602238090053864454166309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15068158726702576302777539 22602238090053864454166309)
                    ·
                      refine ⟨4237919641885099585156183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22602238090053864454166309 4237919641885099585156183)
                      ·
                        rfl

theorem cell23_8253319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_8253319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253319 prefixEnd_8253319 := by exact prefixLift 8253319
  have htrace : WordTrace (prefixWord ++ tailWord_8253319) baseStart_8253319 baseEnd_8253319 := by
    simpa [prefixWord, tailWord_8253319, baseEnd_8253319] using wordTrace_append hprefix tailTrace_8253319
  have hstable : (prefixWord ++ tailWord_8253319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253319).length < 2 ^ (prefixWord ++ tailWord_8253319).sum := by decide
  have hdescent : baseEnd_8253319 < baseStart_8253319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253369 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_8253369 : Nat := 118140960795 + 8253369 * 2 ^ 59
def prefixEnd_8253369 : Nat := 4983230072969 + 3 ^ 40 * 8253369 * 2
def baseEnd_8253369 : Nat := 4237945315917824389530953

theorem tailTrace_8253369 : CollatzResearch.WordTrace tailWord_8253369 prefixEnd_8253369 4237945315917824389530953 := by
  unfold tailWord_8253369
  simp only [CollatzResearch.WordTrace]
  refine ⟨301025097636461151049251161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200683398424307434032834107 301025097636461151049251161)
  ·
    refine ⟨225768823227345863286938371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301025097636461151049251161 225768823227345863286938371)
    ·
      refine ⟨338653234841018794930407557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225768823227345863286938371 338653234841018794930407557)
      ·
        refine ⟨63497481532691024049451417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338653234841018794930407557 63497481532691024049451417)
        ·
          refine ⟨47623111149518268037088563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63497481532691024049451417 47623111149518268037088563)
          ·
            refine ⟨71434666724277402055632845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47623111149518268037088563 71434666724277402055632845)
            ·
              refine ⟨26788000021604025770862317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71434666724277402055632845 26788000021604025770862317)
              ·
                refine ⟨10045500008101509664073369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26788000021604025770862317 10045500008101509664073369)
                ·
                  refine ⟨7534125006076132248055027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10045500008101509664073369 7534125006076132248055027)
                  ·
                    refine ⟨11301187509114198372082541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534125006076132248055027 11301187509114198372082541)
                    ·
                      refine ⟨4237945315917824389530953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11301187509114198372082541 4237945315917824389530953)
                      ·
                        rfl

theorem cell23_8253369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_8253369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253369 prefixEnd_8253369 := by exact prefixLift 8253369
  have htrace : WordTrace (prefixWord ++ tailWord_8253369) baseStart_8253369 baseEnd_8253369 := by
    simpa [prefixWord, tailWord_8253369, baseEnd_8253369] using wordTrace_append hprefix tailTrace_8253369
  have hstable : (prefixWord ++ tailWord_8253369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253369).length < 2 ^ (prefixWord ++ tailWord_8253369).sum := by decide
  have hdescent : baseEnd_8253369 < baseStart_8253369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253392 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2]
def baseStart_8253392 : Nat := 118140960795 + 8253392 * 2 ^ 59
def prefixEnd_8253392 : Nat := 4983230072969 + 3 ^ 40 * 8253392 * 2
def baseEnd_8253392 : Nat := 4237957125972877799543347

theorem tailTrace_8253392 : CollatzResearch.WordTrace tailWord_8253392 prefixEnd_8253392 4237957125972877799543347 := by
  unfold tailWord_8253392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150512968257688912988669215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200683957676918550651558953 150512968257688912988669215)
  ·
    refine ⟨225769452386533369483003823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150512968257688912988669215 225769452386533369483003823)
    ·
      refine ⟨338654178579800054224505735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225769452386533369483003823 338654178579800054224505735)
      ·
        refine ⟨507981267869700081336758603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338654178579800054224505735 507981267869700081336758603)
        ·
          refine ⟨761971901804550122005137905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507981267869700081336758603 761971901804550122005137905)
          ·
            refine ⟨571478926353412591503853429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761971901804550122005137905 571478926353412591503853429)
            ·
              refine ⟨53576149345632430453486259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 571478926353412591503853429 53576149345632430453486259)
              ·
                refine ⟨80364224018448645680229389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53576149345632430453486259 80364224018448645680229389)
                ·
                  refine ⟨30136584006918242130086021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80364224018448645680229389 30136584006918242130086021)
                  ·
                    refine ⟨5650609501297170399391129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30136584006918242130086021 5650609501297170399391129)
                    ·
                      refine ⟨4237957125972877799543347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650609501297170399391129 4237957125972877799543347)
                      ·
                        rfl

theorem cell23_8253392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2].length) (baseStart_8253392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253392 prefixEnd_8253392 := by exact prefixLift 8253392
  have htrace : WordTrace (prefixWord ++ tailWord_8253392) baseStart_8253392 baseEnd_8253392 := by
    simpa [prefixWord, tailWord_8253392, baseEnd_8253392] using wordTrace_append hprefix tailTrace_8253392
  have hstable : (prefixWord ++ tailWord_8253392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253392).length < 2 ^ (prefixWord ++ tailWord_8253392).sum := by decide
  have hdescent : baseEnd_8253392 < baseStart_8253392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253409 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_8253409 : Nat := 118140960795 + 8253409 * 2 ^ 59
def prefixEnd_8253409 : Nat := 4983230072969 + 3 ^ 40 * 8253409 * 2
def baseEnd_8253409 : Nat := 4237965855144004233030769

theorem tailTrace_8253409 : CollatzResearch.WordTrace tailWord_8253409 prefixEnd_8253409 4237965855144004233030769 := by
  unfold tailWord_8253409
  simp only [CollatzResearch.WordTrace]
  refine ⟨301026556556316237880707281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200684371037544158587138187 301026556556316237880707281)
  ·
    refine ⟨225769917417237178410530461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301026556556316237880707281 225769917417237178410530461)
    ·
      refine ⟨84663719031463941903948923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225769917417237178410530461 84663719031463941903948923)
      ·
        refine ⟨126995578547195912855923385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84663719031463941903948923 126995578547195912855923385)
        ·
          refine ⟨95246683910396934641942539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126995578547195912855923385 95246683910396934641942539)
          ·
            refine ⟨142870025865595401962913809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95246683910396934641942539 142870025865595401962913809)
            ·
              refine ⟨107152519399196551472185357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142870025865595401962913809 107152519399196551472185357)
              ·
                refine ⟨40182194774698706802069509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107152519399196551472185357 40182194774698706802069509)
                ·
                  refine ⟨7534161520256007525388033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40182194774698706802069509 7534161520256007525388033)
                  ·
                    refine ⟨5650621140192005644041025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534161520256007525388033 5650621140192005644041025)
                    ·
                      refine ⟨4237965855144004233030769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650621140192005644041025 4237965855144004233030769)
                      ·
                        rfl

theorem cell23_8253409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_8253409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253409 prefixEnd_8253409 := by exact prefixLift 8253409
  have htrace : WordTrace (prefixWord ++ tailWord_8253409) baseStart_8253409 baseEnd_8253409 := by
    simpa [prefixWord, tailWord_8253409, baseEnd_8253409] using wordTrace_append hprefix tailTrace_8253409
  have hstable : (prefixWord ++ tailWord_8253409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253409).length < 2 ^ (prefixWord ++ tailWord_8253409).sum := by decide
  have hdescent : baseEnd_8253409 < baseStart_8253409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253422 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_8253422 : Nat := 118140960795 + 8253422 * 2 ^ 59
def prefixEnd_8253422 : Nat := 4983230072969 + 3 ^ 40 * 8253422 * 2
def baseEnd_8253422 : Nat := 4237972530392512682168209

theorem tailTrace_8253422 : CollatzResearch.WordTrace tailWord_8253422 prefixEnd_8253422 4237972530392512682168209 := by
  unfold tailWord_8253422
  simp only [CollatzResearch.WordTrace]
  refine ⟨37628378838158642637616315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200684687136846094067287013 37628378838158642637616315)
  ·
    refine ⟨56442568257237963956424473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37628378838158642637616315 56442568257237963956424473)
    ·
      refine ⟨42331926192928472967318355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56442568257237963956424473 42331926192928472967318355)
      ·
        refine ⟨63497889289392709450977533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42331926192928472967318355 63497889289392709450977533)
        ·
          refine ⟨23811708483522266044116575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63497889289392709450977533 23811708483522266044116575)
          ·
            refine ⟨35717562725283399066174863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23811708483522266044116575 35717562725283399066174863)
            ·
              refine ⟨53576344087925098599262295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35717562725283399066174863 53576344087925098599262295)
              ·
                refine ⟨80364516131887647898893443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53576344087925098599262295 80364516131887647898893443)
                ·
                  refine ⟨120546774197831471848340165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80364516131887647898893443 120546774197831471848340165)
                  ·
                    refine ⟨22602520162093400971563781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120546774197831471848340165 22602520162093400971563781)
                    ·
                      refine ⟨4237972530392512682168209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22602520162093400971563781 4237972530392512682168209)
                      ·
                        rfl

theorem cell23_8253422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_8253422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253422 prefixEnd_8253422 := by exact prefixLift 8253422
  have htrace : WordTrace (prefixWord ++ tailWord_8253422) baseStart_8253422 baseEnd_8253422 := by
    simpa [prefixWord, tailWord_8253422, baseEnd_8253422] using wordTrace_append hprefix tailTrace_8253422
  have hstable : (prefixWord ++ tailWord_8253422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253422).length < 2 ^ (prefixWord ++ tailWord_8253422).sum := by decide
  have hdescent : baseEnd_8253422 < baseStart_8253422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253460 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_8253460 : Nat := 118140960795 + 8253460 * 2 ^ 59
def prefixEnd_8253460 : Nat := 4983230072969 + 3 ^ 40 * 8253460 * 2
def baseEnd_8253460 : Nat := 4237992042657383533493035

theorem tailTrace_8253460 : CollatzResearch.WordTrace tailWord_8253460 prefixEnd_8253460 4237992042657383533493035 := by
  unfold tailWord_8253460
  simp only [CollatzResearch.WordTrace]
  refine ⟨150514208339565736795406917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200685611119420982393875889 150514208339565736795406917)
  ·
    refine ⟨28221414063668575649138797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150514208339565736795406917 28221414063668575649138797)
    ·
      refine ⟨10583030273875715868427049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28221414063668575649138797 10583030273875715868427049)
      ·
        refine ⟨7937272705406786901320287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10583030273875715868427049 7937272705406786901320287)
        ·
          refine ⟨11905909058110180351980431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937272705406786901320287 11905909058110180351980431)
          ·
            refine ⟨17858863587165270527970647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905909058110180351980431 17858863587165270527970647)
            ·
              refine ⟨26788295380747905791955971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17858863587165270527970647 26788295380747905791955971)
              ·
                refine ⟨40182443071121858687933957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26788295380747905791955971 40182443071121858687933957)
                ·
                  refine ⟨7534208075835348503987617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40182443071121858687933957 7534208075835348503987617)
                  ·
                    refine ⟨5650656056876511377990713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534208075835348503987617 5650656056876511377990713)
                    ·
                      refine ⟨4237992042657383533493035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650656056876511377990713 4237992042657383533493035)
                      ·
                        rfl

theorem cell23_8253460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_8253460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253460 prefixEnd_8253460 := by exact prefixLift 8253460
  have htrace : WordTrace (prefixWord ++ tailWord_8253460) baseStart_8253460 baseEnd_8253460 := by
    simpa [prefixWord, tailWord_8253460, baseEnd_8253460] using wordTrace_append hprefix tailTrace_8253460
  have hstable : (prefixWord ++ tailWord_8253460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253460).length < 2 ^ (prefixWord ++ tailWord_8253460).sum := by decide
  have hdescent : baseEnd_8253460 < baseStart_8253460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253539 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 6]
def baseStart_8253539 : Nat := 118140960795 + 8253539 * 2 ^ 59
def prefixEnd_8253539 : Nat := 4983230072969 + 3 ^ 40 * 8253539 * 2
def baseEnd_8253539 : Nat := 470892511958787636045019

theorem tailTrace_8253539 : CollatzResearch.WordTrace tailWord_8253539 prefixEnd_8253539 470892511958787636045019 := by
  unfold tailWord_8253539
  simp only [CollatzResearch.WordTrace]
  refine ⟨301031298045845270082939671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200687532030563513388626447 301031298045845270082939671)
  ·
    refine ⟨451546947068767905124409507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301031298045845270082939671 451546947068767905124409507)
    ·
      refine ⟨677320420603151857686614261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451546947068767905124409507 677320420603151857686614261)
      ·
        refine ⟨63498789431545486658120087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 677320420603151857686614261 63498789431545486658120087)
        ·
          refine ⟨95248184147318229987180131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63498789431545486658120087 95248184147318229987180131)
          ·
            refine ⟨142872276220977344980770197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95248184147318229987180131 142872276220977344980770197)
            ·
              refine ⟨6697137947858313045973603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142872276220977344980770197 6697137947858313045973603)
              ·
                refine ⟨10045706921787469568960405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697137947858313045973603 10045706921787469568960405)
                ·
                  refine ⟨470892511958787636045019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10045706921787469568960405 470892511958787636045019)
                  ·
                    rfl

theorem cell23_8253539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 6].length) (baseStart_8253539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253539 prefixEnd_8253539 := by exact prefixLift 8253539
  have htrace : WordTrace (prefixWord ++ tailWord_8253539) baseStart_8253539 baseEnd_8253539 := by
    simpa [prefixWord, tailWord_8253539, baseEnd_8253539] using wordTrace_append hprefix tailTrace_8253539
  have hstable : (prefixWord ++ tailWord_8253539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253539).length < 2 ^ (prefixWord ++ tailWord_8253539).sum := by decide
  have hdescent : baseEnd_8253539 < baseStart_8253539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253599 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 6]
def baseStart_8253599 : Nat := 118140960795 + 8253599 * 2 ^ 59
def prefixEnd_8253599 : Nat := 4983230072969 + 3 ^ 40 * 8253599 * 2
def baseEnd_8253599 : Nat := 1412687805489452829884965

theorem tailTrace_8253599 : CollatzResearch.WordTrace tailWord_8253599 prefixEnd_8253599 1412687805489452829884965 := by
  unfold tailWord_8253599
  simp only [CollatzResearch.WordTrace]
  refine ⟨301033486425627900330123851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200688990950418600220082567 301033486425627900330123851)
  ·
    refine ⟨451550229638441850495185777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301033486425627900330123851 451550229638441850495185777)
    ·
      refine ⟨338662672228831387871389333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451550229638441850495185777 338662672228831387871389333)
      ·
        refine ⟨15874812760726471306471375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338662672228831387871389333 15874812760726471306471375)
        ·
          refine ⟨23812219141089706959707063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874812760726471306471375 23812219141089706959707063)
          ·
            refine ⟨35718328711634560439560595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23812219141089706959707063 35718328711634560439560595)
            ·
              refine ⟨53577493067451840659340893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35718328711634560439560595 53577493067451840659340893)
              ·
                refine ⟨20091559900294440247252835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53577493067451840659340893 20091559900294440247252835)
                ·
                  refine ⟨30137339850441660370879253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20091559900294440247252835 30137339850441660370879253)
                  ·
                    refine ⟨1412687805489452829884965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30137339850441660370879253 1412687805489452829884965)
                    ·
                      rfl

theorem cell23_8253599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_8253599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253599 prefixEnd_8253599 := by exact prefixLift 8253599
  have htrace : WordTrace (prefixWord ++ tailWord_8253599) baseStart_8253599 baseEnd_8253599 := by
    simpa [prefixWord, tailWord_8253599, baseEnd_8253599] using wordTrace_append hprefix tailTrace_8253599
  have hstable : (prefixWord ++ tailWord_8253599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253599).length < 2 ^ (prefixWord ++ tailWord_8253599).sum := by decide
  have hdescent : baseEnd_8253599 < baseStart_8253599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253623 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_8253623 : Nat := 118140960795 + 8253623 * 2 ^ 59
def prefixEnd_8253623 : Nat := 4983230072969 + 3 ^ 40 * 8253623 * 2
def baseEnd_8253623 : Nat := 4238075740004066395754785

theorem tailTrace_8253623 : CollatzResearch.WordTrace tailWord_8253623 prefixEnd_8253623 4238075740004066395754785 := by
  unfold tailWord_8253623
  simp only [CollatzResearch.WordTrace]
  refine ⟨301034361777540952428997523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200689574518360634952665015 301034361777540952428997523)
  ·
    refine ⟨451551542666311428643496285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301034361777540952428997523 451551542666311428643496285)
    ·
      refine ⟨169331828499866785741311107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451551542666311428643496285 169331828499866785741311107)
      ·
        refine ⟨253997742749800178611966661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169331828499866785741311107 253997742749800178611966661)
        ·
          refine ⟨47624576765587533489743749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253997742749800178611966661 47624576765587533489743749)
          ·
            refine ⟨8929608143547662529326953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47624576765587533489743749 8929608143547662529326953)
            ·
              refine ⟨6697206107660746896995215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929608143547662529326953 6697206107660746896995215)
              ·
                refine ⟨10045809161491120345492823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697206107660746896995215 10045809161491120345492823)
                ·
                  refine ⟨15068713742236680518239235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10045809161491120345492823 15068713742236680518239235)
                  ·
                    refine ⟨22603070613355020777358853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15068713742236680518239235 22603070613355020777358853)
                    ·
                      refine ⟨4238075740004066395754785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22603070613355020777358853 4238075740004066395754785)
                      ·
                        rfl

theorem cell23_8253623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_8253623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253623 prefixEnd_8253623 := by exact prefixLift 8253623
  have htrace : WordTrace (prefixWord ++ tailWord_8253623) baseStart_8253623 baseEnd_8253623 := by
    simpa [prefixWord, tailWord_8253623, baseEnd_8253623] using wordTrace_append hprefix tailTrace_8253623
  have hstable : (prefixWord ++ tailWord_8253623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253623).length < 2 ^ (prefixWord ++ tailWord_8253623).sum := by decide
  have hdescent : baseEnd_8253623 < baseStart_8253623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253633 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8253633 : Nat := 118140960795 + 8253633 * 2 ^ 59
def prefixEnd_8253633 : Nat := 4983230072969 + 3 ^ 40 * 8253633 * 2
def baseEnd_8253633 : Nat := 1412693624936870452209913

theorem tailTrace_8253633 : CollatzResearch.WordTrace tailWord_8253633 prefixEnd_8253633 1412693624936870452209913 := by
  unfold tailWord_8253633
  simp only [CollatzResearch.WordTrace]
  refine ⟨301034726507504724136861553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200689817671669816091241035 301034726507504724136861553)
  ·
    refine ⟨225776044880628543102646165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301034726507504724136861553 225776044880628543102646165)
    ·
      refine ⟨10583252103779462957936539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225776044880628543102646165 10583252103779462957936539)
      ·
        refine ⟨15874878155669194436904809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10583252103779462957936539 15874878155669194436904809)
        ·
          refine ⟨11906158616751895827678607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15874878155669194436904809 11906158616751895827678607)
          ·
            refine ⟨17859237925127843741517911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906158616751895827678607 17859237925127843741517911)
            ·
              refine ⟨26788856887691765612276867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17859237925127843741517911 26788856887691765612276867)
              ·
                refine ⟨40183285331537648418415301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26788856887691765612276867 40183285331537648418415301)
                ·
                  refine ⟨7534365999663309078452869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40183285331537648418415301 7534365999663309078452869)
                  ·
                    refine ⟨1412693624936870452209913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7534365999663309078452869 1412693624936870452209913)
                    ·
                      rfl

theorem cell23_8253633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8253633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253633 prefixEnd_8253633 := by exact prefixLift 8253633
  have htrace : WordTrace (prefixWord ++ tailWord_8253633) baseStart_8253633 baseEnd_8253633 := by
    simpa [prefixWord, tailWord_8253633, baseEnd_8253633] using wordTrace_append hprefix tailTrace_8253633
  have hstable : (prefixWord ++ tailWord_8253633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253633).length < 2 ^ (prefixWord ++ tailWord_8253633).sum := by decide
  have hdescent : baseEnd_8253633 < baseStart_8253633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253653 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8253653 : Nat := 118140960795 + 8253653 * 2 ^ 59
def prefixEnd_8253653 : Nat := 4983230072969 + 3 ^ 40 * 8253653 * 2
def baseEnd_8253653 : Nat := 4238091144423701278379647

theorem tailTrace_8253653 : CollatzResearch.WordTrace tailWord_8253653 prefixEnd_8253653 4238091144423701278379647 := by
  unfold tailWord_8253653
  simp only [CollatzResearch.WordTrace]
  refine ⟨301035455967432267552589613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200690303978288178368393075 301035455967432267552589613)
  ·
    refine ⟨112888295987787100332221105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301035455967432267552589613 112888295987787100332221105)
    ·
      refine ⟨84666221990840325249165829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112888295987787100332221105 84666221990840325249165829)
      ·
        refine ⟨15874916623282560984218593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84666221990840325249165829 15874916623282560984218593)
        ·
          refine ⟨11906187467461920738163945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15874916623282560984218593 11906187467461920738163945)
          ·
            refine ⟨8929640600596440553622959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11906187467461920738163945 8929640600596440553622959)
            ·
              refine ⟨13394460900894660830434439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929640600596440553622959 13394460900894660830434439)
              ·
                refine ⟨20091691351341991245651659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394460900894660830434439 20091691351341991245651659)
                ·
                  refine ⟨30137537027012986868477489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20091691351341991245651659 30137537027012986868477489)
                  ·
                    refine ⟨22603152770259740151358117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30137537027012986868477489 22603152770259740151358117)
                    ·
                      refine ⟨4238091144423701278379647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22603152770259740151358117 4238091144423701278379647)
                      ·
                        rfl

theorem cell23_8253653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8253653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253653 prefixEnd_8253653 := by exact prefixLift 8253653
  have htrace : WordTrace (prefixWord ++ tailWord_8253653) baseStart_8253653 baseEnd_8253653 := by
    simpa [prefixWord, tailWord_8253653, baseEnd_8253653] using wordTrace_append hprefix tailTrace_8253653
  have hstable : (prefixWord ++ tailWord_8253653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253653).length < 2 ^ (prefixWord ++ tailWord_8253653).sum := by decide
  have hdescent : baseEnd_8253653 < baseStart_8253653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253656 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_8253656 : Nat := 118140960795 + 8253656 * 2 ^ 59
def prefixEnd_8253656 : Nat := 4983230072969 + 3 ^ 40 * 8253656 * 2
def baseEnd_8253656 : Nat := 4238092684865664766642133

theorem tailTrace_8253656 : CollatzResearch.WordTrace tailWord_8253656 prefixEnd_8253656 4238092684865664766642133 := by
  unfold tailWord_8253656
  simp only [CollatzResearch.WordTrace]
  refine ⟨150517782693210699532474411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200690376924280932709965881 150517782693210699532474411)
  ·
    refine ⟨225776674039816049298711617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150517782693210699532474411 225776674039816049298711617)
    ·
      refine ⟨169332505529862036974033713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225776674039816049298711617 169332505529862036974033713)
      ·
        refine ⟨126999379147396527730525285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169332505529862036974033713 126999379147396527730525285)
        ·
          refine ⟨23812383590136848949473491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126999379147396527730525285 23812383590136848949473491)
          ·
            refine ⟨35718575385205273424210237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23812383590136848949473491 35718575385205273424210237)
            ·
              refine ⟨13394465769451977534078839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35718575385205273424210237 13394465769451977534078839)
              ·
                refine ⟨20091698654177966301118259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394465769451977534078839 20091698654177966301118259)
                ·
                  refine ⟨30137547981266949451677389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20091698654177966301118259 30137547981266949451677389)
                  ·
                    refine ⟨11301580492975106044379021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30137547981266949451677389 11301580492975106044379021)
                    ·
                      refine ⟨4238092684865664766642133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11301580492975106044379021 4238092684865664766642133)
                      ·
                        rfl

theorem cell23_8253656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_8253656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253656 prefixEnd_8253656 := by exact prefixLift 8253656
  have htrace : WordTrace (prefixWord ++ tailWord_8253656) baseStart_8253656 baseEnd_8253656 := by
    simpa [prefixWord, tailWord_8253656, baseEnd_8253656] using wordTrace_append hprefix tailTrace_8253656
  have hstable : (prefixWord ++ tailWord_8253656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253656).length < 2 ^ (prefixWord ++ tailWord_8253656).sum := by decide
  have hdescent : baseEnd_8253656 < baseStart_8253656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253669 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_8253669 : Nat := 118140960795 + 8253669 * 2 ^ 59
def prefixEnd_8253669 : Nat := 4983230072969 + 3 ^ 40 * 8253669 * 2
def baseEnd_8253669 : Nat := 4238099360114173215779573

theorem tailTrace_8253669 : CollatzResearch.WordTrace tailWord_8253669 prefixEnd_8253669 4238099360114173215779573 := by
  unfold tailWord_8253669
  simp only [CollatzResearch.WordTrace]
  refine ⟨301036039535374302285172061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200690693023582868190114707 301036039535374302285172061)
  ·
    refine ⟨112888514825765363356939523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301036039535374302285172061 112888514825765363356939523)
    ·
      refine ⟨169332772238648045035409285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112888514825765363356939523 169332772238648045035409285)
      ·
        refine ⟨31749894794746508444139241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169332772238648045035409285 31749894794746508444139241)
        ·
          refine ⟨23812421096059881333104431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31749894794746508444139241 23812421096059881333104431)
          ·
            refine ⟨35718631644089821999656647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23812421096059881333104431 35718631644089821999656647)
            ·
              refine ⟨53577947466134732999484971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35718631644089821999656647 53577947466134732999484971)
              ·
                refine ⟨80366921199202099499227457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53577947466134732999484971 80366921199202099499227457)
                ·
                  refine ⟨60275190899401574624420593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80366921199202099499227457 60275190899401574624420593)
                  ·
                    refine ⟨45206393174551180968315445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60275190899401574624420593 45206393174551180968315445)
                    ·
                      refine ⟨4238099360114173215779573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45206393174551180968315445 4238099360114173215779573)
                      ·
                        rfl

theorem cell23_8253669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_8253669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253669 prefixEnd_8253669 := by exact prefixLift 8253669
  have htrace : WordTrace (prefixWord ++ tailWord_8253669) baseStart_8253669 baseEnd_8253669 := by
    simpa [prefixWord, tailWord_8253669, baseEnd_8253669] using wordTrace_append hprefix tailTrace_8253669
  have hstable : (prefixWord ++ tailWord_8253669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253669).length < 2 ^ (prefixWord ++ tailWord_8253669).sum := by decide
  have hdescent : baseEnd_8253669 < baseStart_8253669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253699 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3]
def baseStart_8253699 : Nat := 118140960795 + 8253699 * 2 ^ 59
def prefixEnd_8253699 : Nat := 4983230072969 + 3 ^ 40 * 8253699 * 2
def baseEnd_8253699 : Nat := 4238114764533808098404435

theorem tailTrace_8253699 : CollatzResearch.WordTrace tailWord_8253699 prefixEnd_8253699 4238114764533808098404435 := by
  unfold tailWord_8253699
  simp only [CollatzResearch.WordTrace]
  refine ⟨301037133725265617408764151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200691422483510411605842767 301037133725265617408764151)
  ·
    refine ⟨451555700587898426113146227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301037133725265617408764151 451555700587898426113146227)
    ·
      refine ⟨677333550881847639169719341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451555700587898426113146227 677333550881847639169719341)
      ·
        refine ⟨254000081580692864688644753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677333550881847639169719341 254000081580692864688644753)
        ·
          refine ⟨190500061185519648516483565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254000081580692864688644753 190500061185519648516483565)
          ·
            refine ⟨71437522944569868193681337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190500061185519648516483565 71437522944569868193681337)
            ·
              refine ⟨53578142208427401145261003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71437522944569868193681337 53578142208427401145261003)
              ·
                refine ⟨80367213312641101717891505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53578142208427401145261003 80367213312641101717891505)
                ·
                  refine ⟨60275409984480826288418629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80367213312641101717891505 60275409984480826288418629)
                  ·
                    refine ⟨11301639372090154929078493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60275409984480826288418629 11301639372090154929078493)
                    ·
                      refine ⟨4238114764533808098404435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11301639372090154929078493 4238114764533808098404435)
                      ·
                        rfl

theorem cell23_8253699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_8253699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253699 prefixEnd_8253699 := by exact prefixLift 8253699
  have htrace : WordTrace (prefixWord ++ tailWord_8253699) baseStart_8253699 baseEnd_8253699 := by
    simpa [prefixWord, tailWord_8253699, baseEnd_8253699] using wordTrace_append hprefix tailTrace_8253699
  have hstable : (prefixWord ++ tailWord_8253699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253699).length < 2 ^ (prefixWord ++ tailWord_8253699).sum := by decide
  have hdescent : baseEnd_8253699 < baseStart_8253699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253753 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 5]
def baseStart_8253753 : Nat := 118140960795 + 8253753 * 2 ^ 59
def prefixEnd_8253753 : Nat := 4983230072969 + 3 ^ 40 * 8253753 * 2
def baseEnd_8253753 : Nat := 470904721387683431903243

theorem tailTrace_8253753 : CollatzResearch.WordTrace tailWord_8253753 prefixEnd_8253753 470904721387683431903243 := by
  unfold tailWord_8253753
  simp only [CollatzResearch.WordTrace]
  refine ⟨301039103267069984631229913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200692735511379989754153275 301039103267069984631229913)
  ·
    refine ⟨225779327450302488473422435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301039103267069984631229913 225779327450302488473422435)
    ·
      refine ⟨338668991175453732710133653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225779327450302488473422435 338668991175453732710133653)
      ·
        refine ⟨15875108961349393720787515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338668991175453732710133653 15875108961349393720787515)
        ·
          refine ⟨23812663442024090581181273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875108961349393720787515 23812663442024090581181273)
          ·
            refine ⟨17859497581518067935885955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23812663442024090581181273 17859497581518067935885955)
            ·
              refine ⟨26789246372277101903828933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17859497581518067935885955 26789246372277101903828933)
              ·
                refine ⟨5022983694801956606967925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26789246372277101903828933 5022983694801956606967925)
                ·
                  refine ⟨470904721387683431903243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022983694801956606967925 470904721387683431903243)
                  ·
                    rfl

theorem cell23_8253753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 5].length) (baseStart_8253753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253753 prefixEnd_8253753 := by exact prefixLift 8253753
  have htrace : WordTrace (prefixWord ++ tailWord_8253753) baseStart_8253753 baseEnd_8253753 := by
    simpa [prefixWord, tailWord_8253753, baseEnd_8253753] using wordTrace_append hprefix tailTrace_8253753
  have hstable : (prefixWord ++ tailWord_8253753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253753).length < 2 ^ (prefixWord ++ tailWord_8253753).sum := by decide
  have hdescent : baseEnd_8253753 < baseStart_8253753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253756 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_8253756 : Nat := 118140960795 + 8253756 * 2 ^ 59
def prefixEnd_8253756 : Nat := 4983230072969 + 3 ^ 40 * 8253756 * 2
def baseEnd_8253756 : Nat := 4238144032931114375391673

theorem tailTrace_8253756 : CollatzResearch.WordTrace tailWord_8253756 prefixEnd_8253756 4238144032931114375391673 := by
  unfold tailWord_8253756
  simp only [CollatzResearch.WordTrace]
  refine ⟨150519606343029558071794561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200692808457372744095726081 150519606343029558071794561)
  ·
    refine ⟨112889704757272168553845921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150519606343029558071794561 112889704757272168553845921)
    ·
      refine ⟨84667278567954126415384441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112889704757272168553845921 84667278567954126415384441)
      ·
        refine ⟨63500458925965594811538331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84667278567954126415384441 63500458925965594811538331)
        ·
          refine ⟨95250688388948392217307497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63500458925965594811538331 95250688388948392217307497)
          ·
            refine ⟨71438016291711294162980623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95250688388948392217307497 71438016291711294162980623)
            ·
              refine ⟨107157024437566941244470935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71438016291711294162980623 107157024437566941244470935)
              ·
                refine ⟨160735536656350411866706403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107157024437566941244470935 160735536656350411866706403)
                ·
                  refine ⟨241103304984525617800059605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160735536656350411866706403 241103304984525617800059605)
                  ·
                    refine ⟨5650858710574819167188897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241103304984525617800059605 5650858710574819167188897)
                    ·
                      refine ⟨4238144032931114375391673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650858710574819167188897 4238144032931114375391673)
                      ·
                        rfl

theorem cell23_8253756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_8253756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253756 prefixEnd_8253756 := by exact prefixLift 8253756
  have htrace : WordTrace (prefixWord ++ tailWord_8253756) baseStart_8253756 baseEnd_8253756 := by
    simpa [prefixWord, tailWord_8253756, baseEnd_8253756] using wordTrace_append hprefix tailTrace_8253756
  have hstable : (prefixWord ++ tailWord_8253756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253756).length < 2 ^ (prefixWord ++ tailWord_8253756).sum := by decide
  have hdescent : baseEnd_8253756 < baseStart_8253756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253759 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_8253759 : Nat := 118140960795 + 8253759 * 2 ^ 59
def prefixEnd_8253759 : Nat := 4983230072969 + 3 ^ 40 * 8253759 * 2
def baseEnd_8253759 : Nat := 4238145573373077863654159

theorem tailTrace_8253759 : CollatzResearch.WordTrace tailWord_8253759 prefixEnd_8253759 4238145573373077863654159 := by
  unfold tailWord_8253759
  simp only [CollatzResearch.WordTrace]
  refine ⟨301039322105048247655948331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200692881403365498437298887 301039322105048247655948331)
  ·
    refine ⟨451558983157572371483922497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301039322105048247655948331 451558983157572371483922497)
    ·
      refine ⟨338669237368179278612941873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451558983157572371483922497 338669237368179278612941873)
      ·
        refine ⟨254001928026134458959706405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338669237368179278612941873 254001928026134458959706405)
        ·
          refine ⟨47625361504900211054944951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254001928026134458959706405 47625361504900211054944951)
          ·
            refine ⟨71438042257350316582417427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47625361504900211054944951 71438042257350316582417427)
            ·
              refine ⟨107157063386025474873626141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71438042257350316582417427 107157063386025474873626141)
              ·
                refine ⟨40183898769759553077609803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107157063386025474873626141 40183898769759553077609803)
                ·
                  refine ⟨60275848154639329616414705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40183898769759553077609803 60275848154639329616414705)
                  ·
                    refine ⟨45206886115979497212311029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60275848154639329616414705 45206886115979497212311029)
                    ·
                      refine ⟨4238145573373077863654159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45206886115979497212311029 4238145573373077863654159)
                      ·
                        rfl

theorem cell23_8253759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_8253759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253759 prefixEnd_8253759 := by exact prefixLift 8253759
  have htrace : WordTrace (prefixWord ++ tailWord_8253759) baseStart_8253759 baseEnd_8253759 := by
    simpa [prefixWord, tailWord_8253759, baseEnd_8253759] using wordTrace_append hprefix tailTrace_8253759
  have hstable : (prefixWord ++ tailWord_8253759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253759).length < 2 ^ (prefixWord ++ tailWord_8253759).sum := by decide
  have hdescent : baseEnd_8253759 < baseStart_8253759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253769 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_8253769 : Nat := 118140960795 + 8253769 * 2 ^ 59
def prefixEnd_8253769 : Nat := 4983230072969 + 3 ^ 40 * 8253769 * 2
def baseEnd_8253769 : Nat := 4238150708179622824529113

theorem tailTrace_8253769 : CollatzResearch.WordTrace tailWord_8253769 prefixEnd_8253769 4238150708179622824529113 := by
  unfold tailWord_8253769
  simp only [CollatzResearch.WordTrace]
  refine ⟨301039686835012019363812361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200693124556674679575874907 301039686835012019363812361)
  ·
    refine ⟨225779765126259014522859271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301039686835012019363812361 225779765126259014522859271)
    ·
      refine ⟨338669647689388521784288907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225779765126259014522859271 338669647689388521784288907)
      ·
        refine ⟨508004471534082782676433361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338669647689388521784288907 508004471534082782676433361)
        ·
          refine ⟨381003353650562087007325021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508004471534082782676433361 381003353650562087007325021)
          ·
            refine ⟨142876257618960782627746883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381003353650562087007325021 142876257618960782627746883)
            ·
              refine ⟨214314386428441173941620325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142876257618960782627746883 214314386428441173941620325)
              ·
                refine ⟨40183947455332720114053811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214314386428441173941620325 40183947455332720114053811)
                ·
                  refine ⟨60275921182999080171080717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40183947455332720114053811 60275921182999080171080717)
                  ·
                    refine ⟨22603470443624655064155269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60275921182999080171080717 22603470443624655064155269)
                    ·
                      refine ⟨4238150708179622824529113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22603470443624655064155269 4238150708179622824529113)
                      ·
                        rfl

theorem cell23_8253769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_8253769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253769 prefixEnd_8253769 := by exact prefixLift 8253769
  have htrace : WordTrace (prefixWord ++ tailWord_8253769) baseStart_8253769 baseEnd_8253769 := by
    simpa [prefixWord, tailWord_8253769, baseEnd_8253769] using wordTrace_append hprefix tailTrace_8253769
  have hstable : (prefixWord ++ tailWord_8253769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253769).length < 2 ^ (prefixWord ++ tailWord_8253769).sum := by decide
  have hdescent : baseEnd_8253769 < baseStart_8253769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253786 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_8253786 : Nat := 118140960795 + 8253786 * 2 ^ 59
def prefixEnd_8253786 : Nat := 4983230072969 + 3 ^ 40 * 8253786 * 2
def baseEnd_8253786 : Nat := 4238159437350749258016535

theorem tailTrace_8253786 : CollatzResearch.WordTrace tailWord_8253786 prefixEnd_8253786 4238159437350749258016535 := by
  unfold tailWord_8253786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75260076718987607816795303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200693537917300287511454141 75260076718987607816795303)
  ·
    refine ⟨112890115078481411725192955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75260076718987607816795303 112890115078481411725192955)
    ·
      refine ⟨169335172617722117587789433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112890115078481411725192955 169335172617722117587789433)
      ·
        refine ⟨127001379463291588190842075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169335172617722117587789433 127001379463291588190842075)
        ·
          refine ⟨190502069194937382286263113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127001379463291588190842075 190502069194937382286263113)
          ·
            refine ⟨142876551896203036714697335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190502069194937382286263113 142876551896203036714697335)
            ·
              refine ⟨214314827844304555072046003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142876551896203036714697335 214314827844304555072046003)
              ·
                refine ⟨321472241766456832608069005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214314827844304555072046003 321472241766456832608069005)
                ·
                  refine ⟨120552090662421312228025877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321472241766456832608069005 120552090662421312228025877)
                  ·
                    refine ⟨5650879249800999010688713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120552090662421312228025877 5650879249800999010688713)
                    ·
                      refine ⟨4238159437350749258016535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5650879249800999010688713 4238159437350749258016535)
                      ·
                        rfl

theorem cell23_8253786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_8253786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253786 prefixEnd_8253786 := by exact prefixLift 8253786
  have htrace : WordTrace (prefixWord ++ tailWord_8253786) baseStart_8253786 baseEnd_8253786 := by
    simpa [prefixWord, tailWord_8253786, baseEnd_8253786] using wordTrace_append hprefix tailTrace_8253786
  have hstable : (prefixWord ++ tailWord_8253786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253786).length < 2 ^ (prefixWord ++ tailWord_8253786).sum := by decide
  have hdescent : baseEnd_8253786 < baseStart_8253786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253796 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_8253796 : Nat := 118140960795 + 8253796 * 2 ^ 59
def prefixEnd_8253796 : Nat := 4983230072969 + 3 ^ 40 * 8253796 * 2
def baseEnd_8253796 : Nat := 1412721524052431406297163

theorem tailTrace_8253796 : CollatzResearch.WordTrace tailWord_8253796 prefixEnd_8253796 1412721524052431406297163 := by
  unfold tailWord_8253796
  simp only [CollatzResearch.WordTrace]
  refine ⟨150520335802957101487522621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200693781070609468650030161 150520335802957101487522621)
  ·
    refine ⟨56445125926108913057820983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150520335802957101487522621 56445125926108913057820983)
    ·
      refine ⟨84667688889163369586731475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56445125926108913057820983 84667688889163369586731475)
      ·
        refine ⟨127001533333745054380097213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84667688889163369586731475 127001533333745054380097213)
        ·
          refine ⟨47625575000154395392536455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127001533333745054380097213 47625575000154395392536455)
          ·
            refine ⟨71438362500231593088804683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47625575000154395392536455 71438362500231593088804683)
            ·
              refine ⟨107157543750347389633207025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71438362500231593088804683 107157543750347389633207025)
              ·
                refine ⟨80368157812760542224905269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107157543750347389633207025 80368157812760542224905269)
                ·
                  refine ⟨7534514794946300833584869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80368157812760542224905269 7534514794946300833584869)
                  ·
                    refine ⟨1412721524052431406297163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7534514794946300833584869 1412721524052431406297163)
                    ·
                      rfl

theorem cell23_8253796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_8253796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253796 prefixEnd_8253796 := by exact prefixLift 8253796
  have htrace : WordTrace (prefixWord ++ tailWord_8253796) baseStart_8253796 baseEnd_8253796 := by
    simpa [prefixWord, tailWord_8253796, baseEnd_8253796] using wordTrace_append hprefix tailTrace_8253796
  have hstable : (prefixWord ++ tailWord_8253796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253796).length < 2 ^ (prefixWord ++ tailWord_8253796).sum := by decide
  have hdescent : baseEnd_8253796 < baseStart_8253796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253813 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_8253813 : Nat := 118140960795 + 8253813 * 2 ^ 59
def prefixEnd_8253813 : Nat := 4983230072969 + 3 ^ 40 * 8253813 * 2
def baseEnd_8253813 : Nat := 1412724433776140217459637

theorem tailTrace_8253813 : CollatzResearch.WordTrace tailWord_8253813 prefixEnd_8253813 1412724433776140217459637 := by
  unfold tailWord_8253813
  simp only [CollatzResearch.WordTrace]
  refine ⟨301041291646852614878414093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200694194431235076585609395 301041291646852614878414093)
  ·
    refine ⟨112890484367569730579405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301041291646852614878414093 112890484367569730579405285)
    ·
      refine ⟨21166965818919324483638491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112890484367569730579405285 21166965818919324483638491)
      ·
        refine ⟨31750448728378986725457737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21166965818919324483638491 31750448728378986725457737)
        ·
          refine ⟨23812836546284240044093303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31750448728378986725457737 23812836546284240044093303)
          ·
            refine ⟨35719254819426360066139955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23812836546284240044093303 35719254819426360066139955)
            ·
              refine ⟨53578882229139540099209933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35719254819426360066139955 53578882229139540099209933)
              ·
                refine ⟨20092080835927327537203725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53578882229139540099209933 20092080835927327537203725)
                ·
                  refine ⟨7534530313472747826451397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20092080835927327537203725 7534530313472747826451397)
                  ·
                    refine ⟨1412724433776140217459637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7534530313472747826451397 1412724433776140217459637)
                    ·
                      rfl

theorem cell23_8253813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_8253813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253813 prefixEnd_8253813 := by exact prefixLift 8253813
  have htrace : WordTrace (prefixWord ++ tailWord_8253813) baseStart_8253813 baseEnd_8253813 := by
    simpa [prefixWord, tailWord_8253813, baseEnd_8253813] using wordTrace_append hprefix tailTrace_8253813
  have hstable : (prefixWord ++ tailWord_8253813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253813).length < 2 ^ (prefixWord ++ tailWord_8253813).sum := by decide
  have hdescent : baseEnd_8253813 < baseStart_8253813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253829 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_8253829 : Nat := 118140960795 + 8253829 * 2 ^ 59
def prefixEnd_8253829 : Nat := 4983230072969 + 3 ^ 40 * 8253829 * 2
def baseEnd_8253829 : Nat := 4238181517018892589778837

theorem tailTrace_8253829 : CollatzResearch.WordTrace tailWord_8253829 prefixEnd_8253829 4238181517018892589778837 := by
  unfold tailWord_8253829
  simp only [CollatzResearch.WordTrace]
  refine ⟨301041875214794649610996541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200694583476529766407331027 301041875214794649610996541)
  ·
    refine ⟨112890703205547993604123703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301041875214794649610996541 112890703205547993604123703)
    ·
      refine ⟨169336054808321990406185555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112890703205547993604123703 169336054808321990406185555)
      ·
        refine ⟨254004082212482985609278333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169336054808321990406185555 254004082212482985609278333)
        ·
          refine ⟨95251530829681119603479375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254004082212482985609278333 95251530829681119603479375)
          ·
            refine ⟨142877296244521679405219063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95251530829681119603479375 142877296244521679405219063)
            ·
              refine ⟨214315944366782519107828595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142877296244521679405219063 214315944366782519107828595)
              ·
                refine ⟨321473916550173778661742893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214315944366782519107828595 321473916550173778661742893)
                ·
                  refine ⟨120552718706315166998153585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321473916550173778661742893 120552718706315166998153585)
                  ·
                    refine ⟨90414539029736375248615189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120552718706315166998153585 90414539029736375248615189)
                    ·
                      refine ⟨4238181517018892589778837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90414539029736375248615189 4238181517018892589778837)
                      ·
                        rfl

theorem cell23_8253829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_8253829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253829 prefixEnd_8253829 := by exact prefixLift 8253829
  have htrace : WordTrace (prefixWord ++ tailWord_8253829) baseStart_8253829 baseEnd_8253829 := by
    simpa [prefixWord, tailWord_8253829, baseEnd_8253829] using wordTrace_append hprefix tailTrace_8253829
  have hstable : (prefixWord ++ tailWord_8253829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253829).length < 2 ^ (prefixWord ++ tailWord_8253829).sum := by decide
  have hdescent : baseEnd_8253829 < baseStart_8253829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253864 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 1, 4]
def baseStart_8253864 : Nat := 118140960795 + 8253864 * 2 ^ 59
def prefixEnd_8253864 : Nat := 4983230072969 + 3 ^ 40 * 8253864 * 2
def baseEnd_8253864 : Nat := 1412733162947266650947059

theorem tailTrace_8253864 : CollatzResearch.WordTrace tailWord_8253864 prefixEnd_8253864 1412733162947266650947059 := by
  unfold tailWord_8253864
  simp only [CollatzResearch.WordTrace]
  refine ⟨150521575884833925294260323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200695434513111900392347097 150521575884833925294260323)
  ·
    refine ⟨225782363827250887941390485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150521575884833925294260323 225782363827250887941390485)
    ·
      refine ⟨10583548304402385372252679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225782363827250887941390485 10583548304402385372252679)
      ·
        refine ⟨15875322456603578058379019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10583548304402385372252679 15875322456603578058379019)
        ·
          refine ⟨23812983684905367087568529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875322456603578058379019 23812983684905367087568529)
          ·
            refine ⟨17859737763679025315676397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23812983684905367087568529 17859737763679025315676397)
            ·
              refine ⟨6697401661379634493378649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17859737763679025315676397 6697401661379634493378649)
              ·
                refine ⟨5023051246034725870033987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697401661379634493378649 5023051246034725870033987)
                ·
                  refine ⟨7534576869052088805050981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023051246034725870033987 7534576869052088805050981)
                  ·
                    refine ⟨1412733162947266650947059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7534576869052088805050981 1412733162947266650947059)
                    ·
                      rfl

theorem cell23_8253864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_8253864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253864 prefixEnd_8253864 := by exact prefixLift 8253864
  have htrace : WordTrace (prefixWord ++ tailWord_8253864) baseStart_8253864 baseEnd_8253864 := by
    simpa [prefixWord, tailWord_8253864, baseEnd_8253864] using wordTrace_append hprefix tailTrace_8253864
  have hstable : (prefixWord ++ tailWord_8253864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253864).length < 2 ^ (prefixWord ++ tailWord_8253864).sum := by decide
  have hdescent : baseEnd_8253864 < baseStart_8253864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253877 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 6]
def baseStart_8253877 : Nat := 118140960795 + 8253877 * 2 ^ 59
def prefixEnd_8253877 : Nat := 4983230072969 + 3 ^ 40 * 8253877 * 2
def baseEnd_8253877 : Nat := 470911796010034266886513

theorem tailTrace_8253877 : CollatzResearch.WordTrace tailWord_8253877 prefixEnd_8253877 470911796010034266886513 := by
  unfold tailWord_8253877
  simp only [CollatzResearch.WordTrace]
  refine ⟨301043625918620753808743885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200695750612413835872495923 301043625918620753808743885)
  ·
    refine ⟨112891359719482782678278957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301043625918620753808743885 112891359719482782678278957)
    ·
      refine ⟨42334259894806043504354609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112891359719482782678278957 42334259894806043504354609)
      ·
        refine ⟨31750694921104532628265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42334259894806043504354609 31750694921104532628265957)
        ·
          refine ⟨5953255297707099867799867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31750694921104532628265957 5953255297707099867799867)
          ·
            refine ⟨8929882946560649801699801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953255297707099867799867 8929882946560649801699801)
            ·
              refine ⟨6697412209920487351274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929882946560649801699801 6697412209920487351274851)
              ·
                refine ⟨10046118314880731026912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697412209920487351274851 10046118314880731026912277)
                ·
                  refine ⟨470911796010034266886513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10046118314880731026912277 470911796010034266886513)
                  ·
                    rfl

theorem cell23_8253877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_8253877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253877 prefixEnd_8253877 := by exact prefixLift 8253877
  have htrace : WordTrace (prefixWord ++ tailWord_8253877) baseStart_8253877 baseEnd_8253877 := by
    simpa [prefixWord, tailWord_8253877, baseEnd_8253877] using wordTrace_append hprefix tailTrace_8253877
  have hstable : (prefixWord ++ tailWord_8253877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253877).length < 2 ^ (prefixWord ++ tailWord_8253877).sum := by decide
  have hdescent : baseEnd_8253877 < baseStart_8253877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253933 : List Nat := [1, 5, 1, 3, 1, 1, 3, 8]
def baseStart_8253933 : Nat := 118140960795 + 8253933 * 2 ^ 59
def prefixEnd_8253933 : Nat := 4983230072969 + 3 ^ 40 * 8253933 * 2
def baseEnd_8253933 : Nat := 156971663666924451217717

theorem tailTrace_8253933 : CollatzResearch.WordTrace tailWord_8253933 prefixEnd_8253933 156971663666924451217717 := by
  unfold tailWord_8253933
  simp only [CollatzResearch.WordTrace]
  refine ⟨301045668406417875372782453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200697112270945250248521635 301045668406417875372782453)
  ·
    refine ⟨28223031413101675816198355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301045668406417875372782453 28223031413101675816198355)
    ·
      refine ⟨42334547119652513724297533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28223031413101675816198355 42334547119652513724297533)
      ·
        refine ⟨15875455169869692646611575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42334547119652513724297533 15875455169869692646611575)
        ·
          refine ⟨23813182754804538969917363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875455169869692646611575 23813182754804538969917363)
          ·
            refine ⟨35719774132206808454876045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23813182754804538969917363 35719774132206808454876045)
            ·
              refine ⟨13394915299577553170578517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35719774132206808454876045 13394915299577553170578517)
              ·
                refine ⟨156971663666924451217717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13394915299577553170578517 156971663666924451217717)
                ·
                  rfl

theorem cell23_8253933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 8].length) (baseStart_8253933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253933 prefixEnd_8253933 := by exact prefixLift 8253933
  have htrace : WordTrace (prefixWord ++ tailWord_8253933) baseStart_8253933 baseEnd_8253933 := by
    simpa [prefixWord, tailWord_8253933, baseEnd_8253933] using wordTrace_append hprefix tailTrace_8253933
  have hstable : (prefixWord ++ tailWord_8253933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253933).length < 2 ^ (prefixWord ++ tailWord_8253933).sum := by decide
  have hdescent : baseEnd_8253933 < baseStart_8253933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8253994 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_8253994 : Nat := 118140960795 + 8253994 * 2 ^ 59
def prefixEnd_8253994 : Nat := 4983230072969 + 3 ^ 40 * 8253994 * 2
def baseEnd_8253994 : Nat := 4238266241326884444215579

theorem tailTrace_8253994 : CollatzResearch.WordTrace tailWord_8253994 prefixEnd_8253994 4238266241326884444215579 := by
  unfold tailWord_8253994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261973314799220697688259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200698595506131255193835357 75261973314799220697688259)
  ·
    refine ⟨112892959972198831046532389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75261973314799220697688259 112892959972198831046532389)
    ·
      refine ⟨21167429994787280821224823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112892959972198831046532389 21167429994787280821224823)
      ·
        refine ⟨31751144992180921231837235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167429994787280821224823 31751144992180921231837235)
        ·
          refine ⟨47626717488271381847755853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31751144992180921231837235 47626717488271381847755853)
          ·
            refine ⟨17860019058101768192908445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47626717488271381847755853 17860019058101768192908445)
            ·
              refine ⟨6697507146788163072340667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17860019058101768192908445 6697507146788163072340667)
              ·
                refine ⟨10046260720182244608511001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697507146788163072340667 10046260720182244608511001)
                ·
                  refine ⟨7534695540136683456383251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046260720182244608511001 7534695540136683456383251)
                  ·
                    refine ⟨11302043310205025184574877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534695540136683456383251 11302043310205025184574877)
                    ·
                      refine ⟨4238266241326884444215579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302043310205025184574877 4238266241326884444215579)
                      ·
                        rfl

theorem cell23_8253994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_8253994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8253994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8253994 prefixEnd_8253994 := by exact prefixLift 8253994
  have htrace : WordTrace (prefixWord ++ tailWord_8253994) baseStart_8253994 baseEnd_8253994 := by
    simpa [prefixWord, tailWord_8253994, baseEnd_8253994] using wordTrace_append hprefix tailTrace_8253994
  have hstable : (prefixWord ++ tailWord_8253994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8253994).length < 2 ^ (prefixWord ++ tailWord_8253994).sum := by decide
  have hdescent : baseEnd_8253994 < baseStart_8253994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8253994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254000 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2]
def baseStart_8254000 : Nat := 118140960795 + 8254000 * 2 ^ 59
def prefixEnd_8254000 : Nat := 4983230072969 + 3 ^ 40 * 8254000 * 2
def baseEnd_8254000 : Nat := 4238269322210811420740551

theorem tailTrace_8254000 : CollatzResearch.WordTrace tailWord_8254000 prefixEnd_8254000 4238269322210811420740551 := by
  unfold tailWord_8254000
  simp only [CollatzResearch.WordTrace]
  refine ⟨150524056048587572907735727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200698741398116763876980969 150524056048587572907735727)
  ·
    refine ⟨225786084072881359361603591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150524056048587572907735727 225786084072881359361603591)
    ·
      refine ⟨338679126109322039042405387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225786084072881359361603591 338679126109322039042405387)
      ·
        refine ⟨508018689163983058563608081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338679126109322039042405387 508018689163983058563608081)
        ·
          refine ⟨381014016872987293922706061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508018689163983058563608081 381014016872987293922706061)
          ·
            refine ⟨142880256327370235221014773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381014016872987293922706061 142880256327370235221014773)
            ·
              refine ⟨13395024030690959551970135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142880256327370235221014773 13395024030690959551970135)
              ·
                refine ⟨20092536046036439327955203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13395024030690959551970135 20092536046036439327955203)
                ·
                  refine ⟨30138804069054658991932805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20092536046036439327955203 30138804069054658991932805)
                  ·
                    refine ⟨5651025762947748560987401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30138804069054658991932805 5651025762947748560987401)
                    ·
                      refine ⟨4238269322210811420740551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651025762947748560987401 4238269322210811420740551)
                      ·
                        rfl

theorem cell23_8254000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2].length) (baseStart_8254000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254000 prefixEnd_8254000 := by exact prefixLift 8254000
  have htrace : WordTrace (prefixWord ++ tailWord_8254000) baseStart_8254000 baseEnd_8254000 := by
    simpa [prefixWord, tailWord_8254000, baseEnd_8254000] using wordTrace_append hprefix tailTrace_8254000
  have hstable : (prefixWord ++ tailWord_8254000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254000).length < 2 ^ (prefixWord ++ tailWord_8254000).sum := by decide
  have hdescent : baseEnd_8254000 < baseStart_8254000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254017 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_8254017 : Nat := 118140960795 + 8254017 * 2 ^ 59
def prefixEnd_8254017 : Nat := 4983230072969 + 3 ^ 40 * 8254017 * 2
def baseEnd_8254017 : Nat := 4238278051381937854227973

theorem tailTrace_8254017 : CollatzResearch.WordTrace tailWord_8254017 prefixEnd_8254017 4238278051381937854227973 := by
  unfold tailWord_8254017
  simp only [CollatzResearch.WordTrace]
  refine ⟨301048732138113557718840305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200699154758742371812560203 301048732138113557718840305)
  ·
    refine ⟨225786549103585168289130229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301048732138113557718840305 225786549103585168289130229)
    ·
      refine ⟨21167488978461109527105959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225786549103585168289130229 21167488978461109527105959)
      ·
        refine ⟨31751233467691664290658939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167488978461109527105959 31751233467691664290658939)
        ·
          refine ⟨47626850201537496435988409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31751233467691664290658939 47626850201537496435988409)
          ·
            refine ⟨35720137651153122326991307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47626850201537496435988409 35720137651153122326991307)
            ·
              refine ⟨53580206476729683490486961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35720137651153122326991307 53580206476729683490486961)
              ·
                refine ⟨40185154857547262617865221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53580206476729683490486961 40185154857547262617865221)
                ·
                  refine ⟨7534716535790111740849729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40185154857547262617865221 7534716535790111740849729)
                  ·
                    refine ⟨5651037401842583805637297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534716535790111740849729 5651037401842583805637297)
                    ·
                      refine ⟨4238278051381937854227973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651037401842583805637297 4238278051381937854227973)
                      ·
                        rfl

theorem cell23_8254017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_8254017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254017 prefixEnd_8254017 := by exact prefixLift 8254017
  have htrace : WordTrace (prefixWord ++ tailWord_8254017) baseStart_8254017 baseEnd_8254017 := by
    simpa [prefixWord, tailWord_8254017, baseEnd_8254017] using wordTrace_append hprefix tailTrace_8254017
  have hstable : (prefixWord ++ tailWord_8254017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254017).length < 2 ^ (prefixWord ++ tailWord_8254017).sum := by decide
  have hdescent : baseEnd_8254017 < baseStart_8254017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254127 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_8254127 : Nat := 118140960795 + 8254127 * 2 ^ 59
def prefixEnd_8254127 : Nat := 4983230072969 + 3 ^ 40 * 8254127 * 2
def baseEnd_8254127 : Nat := 4238334534253932423852467

theorem tailTrace_8254127 : CollatzResearch.WordTrace tailWord_8254127 prefixEnd_8254127 4238334534253932423852467 := by
  unfold tailWord_8254127
  simp only [CollatzResearch.WordTrace]
  refine ⟨301052744167715046505344635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200701829445143364336896423 301052744167715046505344635)
  ·
    refine ⟨451579116251572569758016953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301052744167715046505344635 451579116251572569758016953)
    ·
      refine ⟨338684337188679427318512715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451579116251572569758016953 338684337188679427318512715)
      ·
        refine ⟨508026505783019140977769073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338684337188679427318512715 508026505783019140977769073)
        ·
          refine ⟨381019879337264355733326805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508026505783019140977769073 381019879337264355733326805)
          ·
            refine ⟨8930153421967133337499847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 381019879337264355733326805 8930153421967133337499847)
            ·
              refine ⟨13395230132950700006249771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930153421967133337499847 13395230132950700006249771)
              ·
                refine ⟨20092845199426050009374657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13395230132950700006249771 20092845199426050009374657)
                ·
                  refine ⟨15069633899569537507030993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20092845199426050009374657 15069633899569537507030993)
                  ·
                    refine ⟨11302225424677153130273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15069633899569537507030993 11302225424677153130273245)
                    ·
                      refine ⟨4238334534253932423852467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302225424677153130273245 4238334534253932423852467)
                      ·
                        rfl

theorem cell23_8254127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_8254127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254127 prefixEnd_8254127 := by exact prefixLift 8254127
  have htrace : WordTrace (prefixWord ++ tailWord_8254127) baseStart_8254127 baseEnd_8254127 := by
    simpa [prefixWord, tailWord_8254127, baseEnd_8254127] using wordTrace_append hprefix tailTrace_8254127
  have hstable : (prefixWord ++ tailWord_8254127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254127).length < 2 ^ (prefixWord ++ tailWord_8254127).sum := by decide
  have hdescent : baseEnd_8254127 < baseStart_8254127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254164 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 6]
def baseStart_8254164 : Nat := 118140960795 + 8254164 * 2 ^ 59
def prefixEnd_8254164 : Nat := 4983230072969 + 3 ^ 40 * 8254164 * 2
def baseEnd_8254164 : Nat := 470928170337572086565533

theorem tailTrace_8254164 : CollatzResearch.WordTrace tailWord_8254164 prefixEnd_8254164 470928170337572086565533 := by
  unfold tailWord_8254164
  simp only [CollatzResearch.WordTrace]
  refine ⟨150527046834290500912220773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200702729112387334549627697 150527046834290500912220773)
  ·
    refine ⟨28223821281429468921041395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150527046834290500912220773 28223821281429468921041395)
    ·
      refine ⟨42335731922144203381562093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28223821281429468921041395 42335731922144203381562093)
      ·
        refine ⟨15875899470804076268085785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42335731922144203381562093 15875899470804076268085785)
        ·
          refine ⟨11906924603103057201064339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15875899470804076268085785 11906924603103057201064339)
          ·
            refine ⟨17860386904654585801596509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906924603103057201064339 17860386904654585801596509)
            ·
              refine ⟨6697645089245469675598691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17860386904654585801596509 6697645089245469675598691)
              ·
                refine ⟨10046467633868204513398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697645089245469675598691 10046467633868204513398037)
                ·
                  refine ⟨470928170337572086565533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10046467633868204513398037 470928170337572086565533)
                  ·
                    rfl

theorem cell23_8254164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_8254164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254164 prefixEnd_8254164 := by exact prefixLift 8254164
  have htrace : WordTrace (prefixWord ++ tailWord_8254164) baseStart_8254164 baseEnd_8254164 := by
    simpa [prefixWord, tailWord_8254164, baseEnd_8254164] using wordTrace_append hprefix tailTrace_8254164
  have hstable : (prefixWord ++ tailWord_8254164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254164).length < 2 ^ (prefixWord ++ tailWord_8254164).sum := by decide
  have hdescent : baseEnd_8254164 < baseStart_8254164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254177 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_8254177 : Nat := 118140960795 + 8254177 * 2 ^ 59
def prefixEnd_8254177 : Nat := 4983230072969 + 3 ^ 40 * 8254177 * 2
def baseEnd_8254177 : Nat := 1412786736095552409409079

theorem tailTrace_8254177 : CollatzResearch.WordTrace tailWord_8254177 prefixEnd_8254177 1412786736095552409409079 := by
  unfold tailWord_8254177
  simp only [CollatzResearch.WordTrace]
  refine ⟨301054567817533905044664785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200703045211689270029776523 301054567817533905044664785)
  ·
    refine ⟨225790925863150428783498589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301054567817533905044664785 225790925863150428783498589)
    ·
      refine ⟨84671597198681410793811971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225790925863150428783498589 84671597198681410793811971)
      ·
        refine ⟨127007395798022116190717957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84671597198681410793811971 127007395798022116190717957)
        ·
          refine ⟨23813886712129146785759617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127007395798022116190717957 23813886712129146785759617)
          ·
            refine ⟨17860415034096860089319713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23813886712129146785759617 17860415034096860089319713)
            ·
              refine ⟨13395311275572645066989785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17860415034096860089319713 13395311275572645066989785)
              ·
                refine ⟨10046483456679483800242339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395311275572645066989785 10046483456679483800242339)
                ·
                  refine ⟨15069725185019225700363509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046483456679483800242339 15069725185019225700363509)
                  ·
                    refine ⟨1412786736095552409409079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15069725185019225700363509 1412786736095552409409079)
                    ·
                      rfl

theorem cell23_8254177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_8254177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254177 prefixEnd_8254177 := by exact prefixLift 8254177
  have htrace : WordTrace (prefixWord ++ tailWord_8254177) baseStart_8254177 baseEnd_8254177 := by
    simpa [prefixWord, tailWord_8254177, baseEnd_8254177] using wordTrace_append hprefix tailTrace_8254177
  have hstable : (prefixWord ++ tailWord_8254177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254177).length < 2 ^ (prefixWord ++ tailWord_8254177).sum := by decide
  have hdescent : baseEnd_8254177 < baseStart_8254177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254191 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 1, 1, 3]
def baseStart_8254191 : Nat := 118140960795 + 8254191 * 2 ^ 59
def prefixEnd_8254191 : Nat := 4983230072969 + 3 ^ 40 * 8254191 * 2
def baseEnd_8254191 : Nat := 4238367397015820173452173

theorem tailTrace_8254191 : CollatzResearch.WordTrace tailWord_8254191 prefixEnd_8254191 4238367397015820173452173 := by
  unfold tailWord_8254191
  simp only [CollatzResearch.WordTrace]
  refine ⟨301055078439483185435674427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200703385626322123623782951 301055078439483185435674427)
  ·
    refine ⟨451582617659224778153511641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301055078439483185435674427 451582617659224778153511641)
    ·
      refine ⟨338686963244418583615133731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451582617659224778153511641 338686963244418583615133731)
      ·
        refine ⟨508030444866627875422700597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338686963244418583615133731 508030444866627875422700597)
        ·
          refine ⟨47627854206246363320878181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 508030444866627875422700597 47627854206246363320878181)
          ·
            refine ⟨8930222663671193122664659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47627854206246363320878181 8930222663671193122664659)
            ·
              refine ⟨13395333995506789683996989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930222663671193122664659 13395333995506789683996989)
              ·
                refine ⟨5023250248315046131498871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13395333995506789683996989 5023250248315046131498871)
                ·
                  refine ⟨7534875372472569197248307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023250248315046131498871 7534875372472569197248307)
                  ·
                    refine ⟨11302313058708853795872461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534875372472569197248307 11302313058708853795872461)
                    ·
                      refine ⟨4238367397015820173452173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302313058708853795872461 4238367397015820173452173)
                      ·
                        rfl

theorem cell23_8254191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 1, 3].length) (baseStart_8254191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254191 prefixEnd_8254191 := by exact prefixLift 8254191
  have htrace : WordTrace (prefixWord ++ tailWord_8254191) baseStart_8254191 baseEnd_8254191 := by
    simpa [prefixWord, tailWord_8254191, baseEnd_8254191] using wordTrace_append hprefix tailTrace_8254191
  have hstable : (prefixWord ++ tailWord_8254191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254191).length < 2 ^ (prefixWord ++ tailWord_8254191).sum := by decide
  have hdescent : baseEnd_8254191 < baseStart_8254191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254200 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_8254200 : Nat := 118140960795 + 8254200 * 2 ^ 59
def prefixEnd_8254200 : Nat := 4983230072969 + 3 ^ 40 * 8254200 * 2
def baseEnd_8254200 : Nat := 4238372018341710638239631

theorem tailTrace_8254200 : CollatzResearch.WordTrace tailWord_8254200 prefixEnd_8254200 4238372018341710638239631 := by
  unfold tailWord_8254200
  simp only [CollatzResearch.WordTrace]
  refine ⟨150527703348225289986376027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200703604464300386648501369 150527703348225289986376027)
  ·
    refine ⟨225791555022337934979564041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150527703348225289986376027 225791555022337934979564041)
    ·
      refine ⟨169343666266753451234673031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225791555022337934979564041 169343666266753451234673031)
      ·
        refine ⟨254015499400130176852009547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169343666266753451234673031 254015499400130176852009547)
        ·
          refine ⟨381023249100195265278014321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254015499400130176852009547 381023249100195265278014321)
          ·
            refine ⟨285767436825146448958510741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381023249100195265278014321 285767436825146448958510741)
            ·
              refine ⟨13395348601178739794930191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 285767436825146448958510741 13395348601178739794930191)
              ·
                refine ⟨20093022901768109692395287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13395348601178739794930191 20093022901768109692395287)
                ·
                  refine ⟨30139534352652164538592931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20093022901768109692395287 30139534352652164538592931)
                  ·
                    refine ⟨45209301528978246807889397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30139534352652164538592931 45209301528978246807889397)
                    ·
                      refine ⟨4238372018341710638239631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45209301528978246807889397 4238372018341710638239631)
                      ·
                        rfl

theorem cell23_8254200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_8254200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254200 prefixEnd_8254200 := by exact prefixLift 8254200
  have htrace : WordTrace (prefixWord ++ tailWord_8254200) baseStart_8254200 baseEnd_8254200 := by
    simpa [prefixWord, tailWord_8254200, baseEnd_8254200] using wordTrace_append hprefix tailTrace_8254200
  have hstable : (prefixWord ++ tailWord_8254200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254200).length < 2 ^ (prefixWord ++ tailWord_8254200).sum := by decide
  have hdescent : baseEnd_8254200 < baseStart_8254200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254223 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_8254223 : Nat := 118140960795 + 8254223 * 2 ^ 59
def prefixEnd_8254223 : Nat := 4983230072969 + 3 ^ 40 * 8254223 * 2
def baseEnd_8254223 : Nat := 4238383828396764048252025

theorem tailTrace_8254223 : CollatzResearch.WordTrace tailWord_8254223 prefixEnd_8254223 4238383828396764048252025 := by
  unfold tailWord_8254223
  simp only [CollatzResearch.WordTrace]
  refine ⟨301056245575367254900839323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200704163716911503267226215 301056245575367254900839323)
  ·
    refine ⟨451584368363050882351258985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301056245575367254900839323 451584368363050882351258985)
    ·
      refine ⟨338688276272288161763444239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451584368363050882351258985 338688276272288161763444239)
      ·
        refine ⟨508032414408432242645166359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338688276272288161763444239 508032414408432242645166359)
        ·
          refine ⟨762048621612648363967749539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508032414408432242645166359 762048621612648363967749539)
          ·
            refine ⟨1143072932418972545951624309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762048621612648363967749539 1143072932418972545951624309)
            ·
              refine ⟨107163087414278676182964779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1143072932418972545951624309 107163087414278676182964779)
              ·
                refine ⟨160744631121418014274447169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107163087414278676182964779 160744631121418014274447169)
                ·
                  refine ⟨120558473341063510705835377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160744631121418014274447169 120558473341063510705835377)
                  ·
                    refine ⟨90418855005797633029376533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120558473341063510705835377 90418855005797633029376533)
                    ·
                      refine ⟨4238383828396764048252025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90418855005797633029376533 4238383828396764048252025)
                      ·
                        rfl

theorem cell23_8254223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_8254223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254223 prefixEnd_8254223 := by exact prefixLift 8254223
  have htrace : WordTrace (prefixWord ++ tailWord_8254223) baseStart_8254223 baseEnd_8254223 := by
    simpa [prefixWord, tailWord_8254223, baseEnd_8254223] using wordTrace_append hprefix tailTrace_8254223
  have hstable : (prefixWord ++ tailWord_8254223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254223).length < 2 ^ (prefixWord ++ tailWord_8254223).sum := by decide
  have hdescent : baseEnd_8254223 < baseStart_8254223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254231 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_8254231 : Nat := 118140960795 + 8254231 * 2 ^ 59
def prefixEnd_8254231 : Nat := 4983230072969 + 3 ^ 40 * 8254231 * 2
def baseEnd_8254231 : Nat := 4238387936242000016951989

theorem tailTrace_8254231 : CollatzResearch.WordTrace tailWord_8254231 prefixEnd_8254231 4238387936242000016951989 := by
  unfold tailWord_8254231
  simp only [CollatzResearch.WordTrace]
  refine ⟨301056537359338272267130547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200704358239558848178087031 301056537359338272267130547)
  ·
    refine ⟨451584806039007408400695821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301056537359338272267130547 451584806039007408400695821)
    ·
      refine ⟨169344302264627778150260933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451584806039007408400695821 169344302264627778150260933)
      ·
        refine ⟨31752056674617708403173925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169344302264627778150260933 31752056674617708403173925)
        ·
          refine ⟨5953510626490820325595111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31752056674617708403173925 5953510626490820325595111)
          ·
            refine ⟨8930265939736230488392667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953510626490820325595111 8930265939736230488392667)
            ·
              refine ⟨13395398909604345732589001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930265939736230488392667 13395398909604345732589001)
              ·
                refine ⟨10046549182203259299441751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395398909604345732589001 10046549182203259299441751)
                ·
                  refine ⟨15069823773304888949162627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046549182203259299441751 15069823773304888949162627)
                  ·
                    refine ⟨22604735659957333423743941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15069823773304888949162627 22604735659957333423743941)
                    ·
                      refine ⟨4238387936242000016951989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22604735659957333423743941 4238387936242000016951989)
                      ·
                        rfl

theorem cell23_8254231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_8254231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254231 prefixEnd_8254231 := by exact prefixLift 8254231
  have htrace : WordTrace (prefixWord ++ tailWord_8254231) baseStart_8254231 baseEnd_8254231 := by
    simpa [prefixWord, tailWord_8254231, baseEnd_8254231] using wordTrace_append hprefix tailTrace_8254231
  have hstable : (prefixWord ++ tailWord_8254231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254231).length < 2 ^ (prefixWord ++ tailWord_8254231).sum := by decide
  have hdescent : baseEnd_8254231 < baseStart_8254231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254233 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_8254233 : Nat := 118140960795 + 8254233 * 2 ^ 59
def prefixEnd_8254233 : Nat := 4983230072969 + 3 ^ 40 * 8254233 * 2
def baseEnd_8254233 : Nat := 1412796321067769669708993

theorem tailTrace_8254233 : CollatzResearch.WordTrace tailWord_8254233 prefixEnd_8254233 1412796321067769669708993 := by
  unfold tailWord_8254233
  simp only [CollatzResearch.WordTrace]
  refine ⟨301056610305331026608703353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200704406870220684405802235 301056610305331026608703353)
  ·
    refine ⟨225792457728998269956527515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301056610305331026608703353 225792457728998269956527515)
    ·
      refine ⟨338688686593497404934791273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225792457728998269956527515 338688686593497404934791273)
      ·
        refine ⟨254016514945123053701093455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338688686593497404934791273 254016514945123053701093455)
        ·
          refine ⟨381024772417684580551640183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254016514945123053701093455 381024772417684580551640183)
          ·
            refine ⟨571537158626526870827460275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381024772417684580551640183 571537158626526870827460275)
            ·
              refine ⟨857305737939790306241190413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571537158626526870827460275 857305737939790306241190413)
              ·
                refine ⟨321489651727421364840446405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857305737939790306241190413 321489651727421364840446405)
                ·
                  refine ⟨60279309698891505907583701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321489651727421364840446405 60279309698891505907583701)
                  ·
                    refine ⟨1412796321067769669708993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60279309698891505907583701 1412796321067769669708993)
                    ·
                      rfl

theorem cell23_8254233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_8254233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254233 prefixEnd_8254233 := by exact prefixLift 8254233
  have htrace : WordTrace (prefixWord ++ tailWord_8254233) baseStart_8254233 baseEnd_8254233 := by
    simpa [prefixWord, tailWord_8254233, baseEnd_8254233] using wordTrace_append hprefix tailTrace_8254233
  have hstable : (prefixWord ++ tailWord_8254233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254233).length < 2 ^ (prefixWord ++ tailWord_8254233).sum := by decide
  have hdescent : baseEnd_8254233 < baseStart_8254233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254264 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_8254264 : Nat := 118140960795 + 8254264 * 2 ^ 59
def prefixEnd_8254264 : Nat := 4983230072969 + 3 ^ 40 * 8254264 * 2
def baseEnd_8254264 : Nat := 4238404881103598387839337

theorem tailTrace_8254264 : CollatzResearch.WordTrace tailWord_8254264 prefixEnd_8254264 4238404881103598387839337 := by
  unfold tailWord_8254264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150528870484109359451540923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200705160645479145935387897 150528870484109359451540923)
  ·
    refine ⟨225793305726164039177311385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150528870484109359451540923 225793305726164039177311385)
    ·
      refine ⟨169344979294623029382983539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225793305726164039177311385 169344979294623029382983539)
      ·
        refine ⟨254017468941934544074475309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169344979294623029382983539 254017468941934544074475309)
        ·
          refine ⟨95256550853225454027928241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254017468941934544074475309 95256550853225454027928241)
          ·
            refine ⟨71442413139919090520946181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95256550853225454027928241 71442413139919090520946181)
            ·
              refine ⟨13395452463734829472677409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71442413139919090520946181 13395452463734829472677409)
              ·
                refine ⟨10046589347801122104508057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395452463734829472677409 10046589347801122104508057)
                ·
                  refine ⟨7534942010850841578381043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046589347801122104508057 7534942010850841578381043)
                  ·
                    refine ⟨11302413016276262367571565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534942010850841578381043 11302413016276262367571565)
                    ·
                      refine ⟨4238404881103598387839337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302413016276262367571565 4238404881103598387839337)
                      ·
                        rfl

theorem cell23_8254264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_8254264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254264 prefixEnd_8254264 := by exact prefixLift 8254264
  have htrace : WordTrace (prefixWord ++ tailWord_8254264) baseStart_8254264 baseEnd_8254264 := by
    simpa [prefixWord, tailWord_8254264, baseEnd_8254264] using wordTrace_append hprefix tailTrace_8254264
  have hstable : (prefixWord ++ tailWord_8254264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254264).length < 2 ^ (prefixWord ++ tailWord_8254264).sum := by decide
  have hdescent : baseEnd_8254264 < baseStart_8254264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254280 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_8254280 : Nat := 118140960795 + 8254280 * 2 ^ 59
def prefixEnd_8254280 : Nat := 4983230072969 + 3 ^ 40 * 8254280 * 2
def baseEnd_8254280 : Nat := 1412804365598023441746421

theorem tailTrace_8254280 : CollatzResearch.WordTrace tailWord_8254280 prefixEnd_8254280 1412804365598023441746421 := by
  unfold tailWord_8254280
  simp only [CollatzResearch.WordTrace]
  refine ⟨150529162268080376817832147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200705549690773835757109529 150529162268080376817832147)
  ·
    refine ⟨225793743402120565226748221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150529162268080376817832147 225793743402120565226748221)
    ·
      refine ⟨84672653775795211960030583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225793743402120565226748221 84672653775795211960030583)
      ·
        refine ⟨127008980663692817940045875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84672653775795211960030583 127008980663692817940045875)
        ·
          refine ⟨190513470995539226910068813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127008980663692817940045875 190513470995539226910068813)
          ·
            refine ⟨71442551623327210091275805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190513470995539226910068813 71442551623327210091275805)
            ·
              refine ⟨26790956858747703784228427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71442551623327210091275805 26790956858747703784228427)
              ·
                refine ⟨40186435288121555676342641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26790956858747703784228427 40186435288121555676342641)
                ·
                  refine ⟨30139826466091166757256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40186435288121555676342641 30139826466091166757256981)
                  ·
                    refine ⟨1412804365598023441746421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30139826466091166757256981 1412804365598023441746421)
                    ·
                      rfl

theorem cell23_8254280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_8254280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254280 prefixEnd_8254280 := by exact prefixLift 8254280
  have htrace : WordTrace (prefixWord ++ tailWord_8254280) baseStart_8254280 baseEnd_8254280 := by
    simpa [prefixWord, tailWord_8254280, baseEnd_8254280] using wordTrace_append hprefix tailTrace_8254280
  have hstable : (prefixWord ++ tailWord_8254280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254280).length < 2 ^ (prefixWord ++ tailWord_8254280).sum := by decide
  have hdescent : baseEnd_8254280 < baseStart_8254280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254304 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2]
def baseStart_8254304 : Nat := 118140960795 + 8254304 * 2 ^ 59
def prefixEnd_8254304 : Nat := 4983230072969 + 3 ^ 40 * 8254304 * 2
def baseEnd_8254304 : Nat := 4238425420329778231339153

theorem tailTrace_8254304 : CollatzResearch.WordTrace tailWord_8254304 prefixEnd_8254304 4238425420329778231339153 := by
  unfold tailWord_8254304
  simp only [CollatzResearch.WordTrace]
  refine ⟨150529599944036902867268983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200706133258715870489691977 150529599944036902867268983)
  ·
    refine ⟨225794399916055354300903475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150529599944036902867268983 225794399916055354300903475)
    ·
      refine ⟨338691599874083031451355213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225794399916055354300903475 338691599874083031451355213)
      ·
        refine ⟨127009349952781136794258205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338691599874083031451355213 127009349952781136794258205)
        ·
          refine ⟨47628506232292926297846827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127009349952781136794258205 47628506232292926297846827)
          ·
            refine ⟨71442759348439389446770241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47628506232292926297846827 71442759348439389446770241)
            ·
              refine ⟨53582069511329542085077681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71442759348439389446770241 53582069511329542085077681)
              ·
                refine ⟨40186552133497156563808261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53582069511329542085077681 40186552133497156563808261)
                ·
                  refine ⟨7534978525030716855714049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40186552133497156563808261 7534978525030716855714049)
                  ·
                    refine ⟨5651233893773037641785537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534978525030716855714049 5651233893773037641785537)
                    ·
                      refine ⟨4238425420329778231339153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651233893773037641785537 4238425420329778231339153)
                      ·
                        rfl

theorem cell23_8254304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_8254304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254304 prefixEnd_8254304 := by exact prefixLift 8254304
  have htrace : WordTrace (prefixWord ++ tailWord_8254304) baseStart_8254304 baseEnd_8254304 := by
    simpa [prefixWord, tailWord_8254304, baseEnd_8254304] using wordTrace_append hprefix tailTrace_8254304
  have hstable : (prefixWord ++ tailWord_8254304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254304).length < 2 ^ (prefixWord ++ tailWord_8254304).sum := by decide
  have hdescent : baseEnd_8254304 < baseStart_8254304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254308 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_8254308 : Nat := 118140960795 + 8254308 * 2 ^ 59
def prefixEnd_8254308 : Nat := 4983230072969 + 3 ^ 40 * 8254308 * 2
def baseEnd_8254308 : Nat := 4238427474252396215689135

theorem tailTrace_8254308 : CollatzResearch.WordTrace tailWord_8254308 prefixEnd_8254308 4238427474252396215689135 := by
  unfold tailWord_8254308
  simp only [CollatzResearch.WordTrace]
  refine ⟨150529672890029657208841789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200706230520039542945122385 150529672890029657208841789)
  ·
    refine ⟨56448627333761121453315671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150529672890029657208841789 56448627333761121453315671)
    ·
      refine ⟨84672941000641682179973507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56448627333761121453315671 84672941000641682179973507)
      ·
        refine ⟨127009411500962523269960261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84672941000641682179973507 127009411500962523269960261)
        ·
          refine ⟨23814264656430473113117549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127009411500962523269960261 23814264656430473113117549)
          ·
            refine ⟨8930349246161427417419081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23814264656430473113117549 8930349246161427417419081)
            ·
              refine ⟨6697761934621070563064311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8930349246161427417419081 6697761934621070563064311)
              ·
                refine ⟨10046642901931605844596467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697761934621070563064311 10046642901931605844596467)
                ·
                  refine ⟨15069964352897408766894701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046642901931605844596467 15069964352897408766894701)
                  ·
                    refine ⟨5651236632336528287585513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15069964352897408766894701 5651236632336528287585513)
                    ·
                      refine ⟨4238427474252396215689135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651236632336528287585513 4238427474252396215689135)
                      ·
                        rfl

theorem cell23_8254308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_8254308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254308 prefixEnd_8254308 := by exact prefixLift 8254308
  have htrace : WordTrace (prefixWord ++ tailWord_8254308) baseStart_8254308 baseEnd_8254308 := by
    simpa [prefixWord, tailWord_8254308, baseEnd_8254308] using wordTrace_append hprefix tailTrace_8254308
  have hstable : (prefixWord ++ tailWord_8254308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254308).length < 2 ^ (prefixWord ++ tailWord_8254308).sum := by decide
  have hdescent : baseEnd_8254308 < baseStart_8254308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254321 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_8254321 : Nat := 118140960795 + 8254321 * 2 ^ 59
def prefixEnd_8254321 : Nat := 4983230072969 + 3 ^ 40 * 8254321 * 2
def baseEnd_8254321 : Nat := 4238434149500904664826575

theorem tailTrace_8254321 : CollatzResearch.WordTrace tailWord_8254321 prefixEnd_8254321 4238434149500904664826575 := by
  unfold tailWord_8254321
  simp only [CollatzResearch.WordTrace]
  refine ⟨301059819929012217637906817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200706546619341478425271211 301059819929012217637906817)
  ·
    refine ⟨225794864946759163228430113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301059819929012217637906817 225794864946759163228430113)
    ·
      refine ⟨169346148710069372421322585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225794864946759163228430113 169346148710069372421322585)
      ·
        refine ⟨127009611532552029315991939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169346148710069372421322585 127009611532552029315991939)
        ·
          refine ⟨190514417298828043973987909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127009611532552029315991939 190514417298828043973987909)
          ·
            refine ⟨35721453243530258245122733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190514417298828043973987909 35721453243530258245122733)
            ·
              refine ⟨13395544966323846841921025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35721453243530258245122733 13395544966323846841921025)
              ·
                refine ⟨10046658724742885131440769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395544966323846841921025 10046658724742885131440769)
                ·
                  refine ⟨7534994043557163848580577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046658724742885131440769 7534994043557163848580577)
                  ·
                    refine ⟨5651245532667872886435433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534994043557163848580577 5651245532667872886435433)
                    ·
                      refine ⟨4238434149500904664826575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651245532667872886435433 4238434149500904664826575)
                      ·
                        rfl

theorem cell23_8254321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_8254321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254321 prefixEnd_8254321 := by exact prefixLift 8254321
  have htrace : WordTrace (prefixWord ++ tailWord_8254321) baseStart_8254321 baseEnd_8254321 := by
    simpa [prefixWord, tailWord_8254321, baseEnd_8254321] using wordTrace_append hprefix tailTrace_8254321
  have hstable : (prefixWord ++ tailWord_8254321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254321).length < 2 ^ (prefixWord ++ tailWord_8254321).sum := by decide
  have hdescent : baseEnd_8254321 < baseStart_8254321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254347 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 5, 2]
def baseStart_8254347 : Nat := 118140960795 + 8254347 * 2 ^ 59
def prefixEnd_8254347 : Nat := 4983230072969 + 3 ^ 40 * 8254347 * 2
def baseEnd_8254347 : Nat := 4238447499997921563101455

theorem tailTrace_8254347 : CollatzResearch.WordTrace tailWord_8254347 prefixEnd_8254347 4238447499997921563101455 := by
  unfold tailWord_8254347
  simp only [CollatzResearch.WordTrace]
  refine ⟨301060768226918024078353295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200707178817945349385568863 301060768226918024078353295)
  ·
    refine ⟨451591152340377036117529943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301060768226918024078353295 451591152340377036117529943)
    ·
      refine ⟨677386728510565554176294915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451591152340377036117529943 677386728510565554176294915)
      ·
        refine ⟨1016080092765848331264442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677386728510565554176294915 1016080092765848331264442373)
        ·
          refine ⟨190515017393596562112082945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016080092765848331264442373 190515017393596562112082945)
          ·
            refine ⟨142886263045197421584062209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190515017393596562112082945 142886263045197421584062209)
            ·
              refine ⟨107164697283898066188046657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142886263045197421584062209 107164697283898066188046657)
              ·
                refine ⟨80373522962923549641034993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107164697283898066188046657 80373522962923549641034993)
                ·
                  refine ⟨60280142222192662230776245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80373522962923549641034993 60280142222192662230776245)
                  ·
                    refine ⟨5651263333330562084135273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60280142222192662230776245 5651263333330562084135273)
                    ·
                      refine ⟨4238447499997921563101455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651263333330562084135273 4238447499997921563101455)
                      ·
                        rfl

theorem cell23_8254347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5, 2].length) (baseStart_8254347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254347 prefixEnd_8254347 := by exact prefixLift 8254347
  have htrace : WordTrace (prefixWord ++ tailWord_8254347) baseStart_8254347 baseEnd_8254347 := by
    simpa [prefixWord, tailWord_8254347, baseEnd_8254347] using wordTrace_append hprefix tailTrace_8254347
  have hstable : (prefixWord ++ tailWord_8254347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254347).length < 2 ^ (prefixWord ++ tailWord_8254347).sum := by decide
  have hdescent : baseEnd_8254347 < baseStart_8254347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254377 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_8254377 : Nat := 118140960795 + 8254377 * 2 ^ 59
def prefixEnd_8254377 : Nat := 4983230072969 + 3 ^ 40 * 8254377 * 2
def baseEnd_8254377 : Nat := 4238462904417556445726317

theorem tailTrace_8254377 : CollatzResearch.WordTrace tailWord_8254377 prefixEnd_8254377 4238462904417556445726317 := by
  unfold tailWord_8254377
  simp only [CollatzResearch.WordTrace]
  refine ⟨301061862416809339201945385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200707908277872892801296923 301061862416809339201945385)
  ·
    refine ⟨225796396812607004401459039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301061862416809339201945385 225796396812607004401459039)
    ·
      refine ⟨338694595218910506602188559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225796396812607004401459039 338694595218910506602188559)
      ·
        refine ⟨508041892828365759903282839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338694595218910506602188559 508041892828365759903282839)
        ·
          refine ⟨762062839242548639854924259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508041892828365759903282839 762062839242548639854924259)
          ·
            refine ⟨1143094258863822959782386389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762062839242548639854924259 1143094258863822959782386389)
            ·
              refine ⟨26791271692120850619899681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1143094258863822959782386389 26791271692120850619899681)
              ·
                refine ⟨20093453769090637964924761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26791271692120850619899681 20093453769090637964924761)
                ·
                  refine ⟨15070090326817978473693571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20093453769090637964924761 15070090326817978473693571)
                  ·
                    refine ⟨22605135490226967710540357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15070090326817978473693571 22605135490226967710540357)
                    ·
                      refine ⟨4238462904417556445726317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22605135490226967710540357 4238462904417556445726317)
                      ·
                        rfl

theorem cell23_8254377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_8254377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254377 prefixEnd_8254377 := by exact prefixLift 8254377
  have htrace : WordTrace (prefixWord ++ tailWord_8254377) baseStart_8254377 baseEnd_8254377 := by
    simpa [prefixWord, tailWord_8254377, baseEnd_8254377] using wordTrace_append hprefix tailTrace_8254377
  have hstable : (prefixWord ++ tailWord_8254377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254377).length < 2 ^ (prefixWord ++ tailWord_8254377).sum := by decide
  have hdescent : baseEnd_8254377 < baseStart_8254377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254380 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_8254380 : Nat := 118140960795 + 8254380 * 2 ^ 59
def prefixEnd_8254380 : Nat := 4983230072969 + 3 ^ 40 * 8254380 * 2
def baseEnd_8254380 : Nat := 4238464444859519933988803

theorem tailTrace_8254380 : CollatzResearch.WordTrace tailWord_8254380 prefixEnd_8254380 4238464444859519933988803 := by
  unfold tailWord_8254380
  simp only [CollatzResearch.WordTrace]
  refine ⟨150530985917899235357152297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200707981223865647142869729 150530985917899235357152297)
  ·
    refine ⟨112898239438424426517864223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150530985917899235357152297 112898239438424426517864223)
    ·
      refine ⟨169347359157636639776796335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112898239438424426517864223 169347359157636639776796335)
      ·
        refine ⟨254021038736454959665194503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169347359157636639776796335 254021038736454959665194503)
        ·
          refine ⟨381031558104682439497791755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254021038736454959665194503 381031558104682439497791755)
          ·
            refine ⟨571547337157023659246687633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381031558104682439497791755 571547337157023659246687633)
            ·
              refine ⟨428660502867767744435015725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571547337157023659246687633 428660502867767744435015725)
              ·
                refine ⟨160747688575412904163130897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428660502867767744435015725 160747688575412904163130897)
                ·
                  refine ⟨120560766431559678122348173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160747688575412904163130897 120560766431559678122348173)
                  ·
                    refine ⟨45210287411834879295880565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120560766431559678122348173 45210287411834879295880565)
                    ·
                      refine ⟨4238464444859519933988803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45210287411834879295880565 4238464444859519933988803)
                      ·
                        rfl

theorem cell23_8254380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_8254380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254380 prefixEnd_8254380 := by exact prefixLift 8254380
  have htrace : WordTrace (prefixWord ++ tailWord_8254380) baseStart_8254380 baseEnd_8254380 := by
    simpa [prefixWord, tailWord_8254380, baseEnd_8254380] using wordTrace_append hprefix tailTrace_8254380
  have hstable : (prefixWord ++ tailWord_8254380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254380).length < 2 ^ (prefixWord ++ tailWord_8254380).sum := by decide
  have hdescent : baseEnd_8254380 < baseStart_8254380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254387 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 3, 4]
def baseStart_8254387 : Nat := 118140960795 + 8254387 * 2 ^ 59
def prefixEnd_8254387 : Nat := 4983230072969 + 3 ^ 40 * 8254387 * 2
def baseEnd_8254387 : Nat := 1412822679741367135533757

theorem tailTrace_8254387 : CollatzResearch.WordTrace tailWord_8254387 prefixEnd_8254387 1412822679741367135533757 := by
  unfold tailWord_8254387
  simp only [CollatzResearch.WordTrace]
  refine ⟨301062227146773110909809415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200708151431182073939872943 301062227146773110909809415)
  ·
    refine ⟨451593340720159666364714123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301062227146773110909809415 451593340720159666364714123)
    ·
      refine ⟨677390011080239499547071185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451593340720159666364714123 677390011080239499547071185)
      ·
        refine ⟨508042508310179624660303389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677390011080239499547071185 508042508310179624660303389)
        ·
          refine ⟨190515940616317359247613771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508042508310179624660303389 190515940616317359247613771)
          ·
            refine ⟨285773910924476038871420657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190515940616317359247613771 285773910924476038871420657)
            ·
              refine ⟨214330433193357029153565493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285773910924476038871420657 214330433193357029153565493)
              ·
                refine ⟨20093478111877221483146765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214330433193357029153565493 20093478111877221483146765)
                ·
                  refine ⟨7535054291953958056180037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20093478111877221483146765 7535054291953958056180037)
                  ·
                    refine ⟨1412822679741367135533757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535054291953958056180037 1412822679741367135533757)
                    ·
                      rfl

theorem cell23_8254387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 4].length) (baseStart_8254387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254387 prefixEnd_8254387 := by exact prefixLift 8254387
  have htrace : WordTrace (prefixWord ++ tailWord_8254387) baseStart_8254387 baseEnd_8254387 := by
    simpa [prefixWord, tailWord_8254387, baseEnd_8254387] using wordTrace_append hprefix tailTrace_8254387
  have hstable : (prefixWord ++ tailWord_8254387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254387).length < 2 ^ (prefixWord ++ tailWord_8254387).sum := by decide
  have hdescent : baseEnd_8254387 < baseStart_8254387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254414 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_8254414 : Nat := 118140960795 + 8254414 * 2 ^ 59
def prefixEnd_8254414 : Nat := 4983230072969 + 3 ^ 40 * 8254414 * 2
def baseEnd_8254414 : Nat := 4238481903201772800963647

theorem tailTrace_8254414 : CollatzResearch.WordTrace tailWord_8254414 prefixEnd_8254414 4238481903201772800963647 := by
  unfold tailWord_8254414
  simp only [CollatzResearch.WordTrace]
  refine ⟨37632901489709411815130287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200708807945116863014028197 37632901489709411815130287)
  ·
    refine ⟨56449352234564117722695431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37632901489709411815130287 56449352234564117722695431)
    ·
      refine ⟨84674028351846176584043147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56449352234564117722695431 84674028351846176584043147)
      ·
        refine ⟨127011042527769264876064721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84674028351846176584043147 127011042527769264876064721)
        ·
          refine ⟨95258281895826948657048541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127011042527769264876064721 95258281895826948657048541)
          ·
            refine ⟨35721855710935105746393203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95258281895826948657048541 35721855710935105746393203)
            ·
              refine ⟨53582783566402658619589805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35721855710935105746393203 53582783566402658619589805)
              ·
                refine ⟨20093543837400996982346177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53582783566402658619589805 20093543837400996982346177)
                ·
                  refine ⟨15070157878050747736759633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20093543837400996982346177 15070157878050747736759633)
                  ·
                    refine ⟨11302618408538060802569725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15070157878050747736759633 11302618408538060802569725)
                    ·
                      refine ⟨4238481903201772800963647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302618408538060802569725 4238481903201772800963647)
                      ·
                        rfl

theorem cell23_8254414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_8254414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254414 prefixEnd_8254414 := by exact prefixLift 8254414
  have htrace : WordTrace (prefixWord ++ tailWord_8254414) baseStart_8254414 baseEnd_8254414 := by
    simpa [prefixWord, tailWord_8254414, baseEnd_8254414] using wordTrace_append hprefix tailTrace_8254414
  have hstable : (prefixWord ++ tailWord_8254414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254414).length < 2 ^ (prefixWord ++ tailWord_8254414).sum := by decide
  have hdescent : baseEnd_8254414 < baseStart_8254414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254447 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 3, 5]
def baseStart_8254447 : Nat := 118140960795 + 8254447 * 2 ^ 59
def prefixEnd_8254447 : Nat := 4983230072969 + 3 ^ 40 * 8254447 * 2
def baseEnd_8254447 : Nat := 1412832949354457057283665

theorem tailTrace_8254447 : CollatzResearch.WordTrace tailWord_8254447 prefixEnd_8254447 1412832949354457057283665 := by
  unfold tailWord_8254447
  simp only [CollatzResearch.WordTrace]
  refine ⟨301064415526555741156993595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200709610351037160771329063 301064415526555741156993595)
  ·
    refine ⟨451596623289833611735490393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301064415526555741156993595 451596623289833611735490393)
    ·
      refine ⟨338697467467375208801617795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451596623289833611735490393 338697467467375208801617795)
      ·
        refine ⟨508046201201062813202426693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338697467467375208801617795 508046201201062813202426693)
        ·
          refine ⟨95258662725199277475455005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508046201201062813202426693 95258662725199277475455005)
          ·
            refine ⟨35721998521949729053295627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95258662725199277475455005 35721998521949729053295627)
            ·
              refine ⟨53582997782924593579943441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35721998521949729053295627 53582997782924593579943441)
              ·
                refine ⟨40187248337193445184957581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53582997782924593579943441 40187248337193445184957581)
                ·
                  refine ⟨15070218126447541944359093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40187248337193445184957581 15070218126447541944359093)
                  ·
                    refine ⟨1412832949354457057283665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15070218126447541944359093 1412832949354457057283665)
                    ·
                      rfl

theorem cell23_8254447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_8254447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254447 prefixEnd_8254447 := by exact prefixLift 8254447
  have htrace : WordTrace (prefixWord ++ tailWord_8254447) baseStart_8254447 baseEnd_8254447 := by
    simpa [prefixWord, tailWord_8254447, baseEnd_8254447] using wordTrace_append hprefix tailTrace_8254447
  have hstable : (prefixWord ++ tailWord_8254447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254447).length < 2 ^ (prefixWord ++ tailWord_8254447).sum := by decide
  have hdescent : baseEnd_8254447 < baseStart_8254447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254478 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_8254478 : Nat := 118140960795 + 8254478 * 2 ^ 59
def prefixEnd_8254478 : Nat := 4983230072969 + 3 ^ 40 * 8254478 * 2
def baseEnd_8254478 : Nat := 4238514765963660550563353

theorem tailTrace_8254478 : CollatzResearch.WordTrace tailWord_8254478 prefixEnd_8254478 4238514765963660550563353 := by
  unfold tailWord_8254478
  simp only [CollatzResearch.WordTrace]
  refine ⟨37633193273680429181421511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200710364126295622300914725 37633193273680429181421511)
  ·
    refine ⟨56449789910520643772132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37633193273680429181421511 56449789910520643772132267)
    ·
      refine ⟨84674684865780965658198401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56449789910520643772132267 84674684865780965658198401)
      ·
        refine ⟨63506013649335724243648801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84674684865780965658198401 63506013649335724243648801)
        ·
          refine ⟨47629510237001793182736601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63506013649335724243648801 47629510237001793182736601)
          ·
            refine ⟨35722132677751344887052451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47629510237001793182736601 35722132677751344887052451)
            ·
              refine ⟨53583199016627017330578677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35722132677751344887052451 53583199016627017330578677)
              ·
                refine ⟨5023424907808782874741751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53583199016627017330578677 5023424907808782874741751)
                ·
                  refine ⟨7535137361713174312112627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023424907808782874741751 7535137361713174312112627)
                  ·
                    refine ⟨11302706042569761468168941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535137361713174312112627 11302706042569761468168941)
                    ·
                      refine ⟨4238514765963660550563353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302706042569761468168941 4238514765963660550563353)
                      ·
                        rfl

theorem cell23_8254478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_8254478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254478 prefixEnd_8254478 := by exact prefixLift 8254478
  have htrace : WordTrace (prefixWord ++ tailWord_8254478) baseStart_8254478 baseEnd_8254478 := by
    simpa [prefixWord, tailWord_8254478, baseEnd_8254478] using wordTrace_append hprefix tailTrace_8254478
  have hstable : (prefixWord ++ tailWord_8254478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254478).length < 2 ^ (prefixWord ++ tailWord_8254478).sum := by decide
  have hdescent : baseEnd_8254478 < baseStart_8254478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254518 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_8254518 : Nat := 118140960795 + 8254518 * 2 ^ 59
def prefixEnd_8254518 : Nat := 4983230072969 + 3 ^ 40 * 8254518 * 2
def baseEnd_8254518 : Nat := 4238535305189840394063169

theorem tailTrace_8254518 : CollatzResearch.WordTrace tailWord_8254518 prefixEnd_8254518 4238535305189840394063169 := by
  unfold tailWord_8254518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816687819331157517676763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200711336739532346855218805 18816687819331157517676763)
  ·
    refine ⟨28225031728996736276515145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18816687819331157517676763 28225031728996736276515145)
    ·
      refine ⟨21168773796747552207386359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28225031728996736276515145 21168773796747552207386359)
      ·
        refine ⟨31753160695121328311079539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21168773796747552207386359 31753160695121328311079539)
        ·
          refine ⟨47629741042681992466619309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31753160695121328311079539 47629741042681992466619309)
          ·
            refine ⟨17861152891005747174982241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47629741042681992466619309 17861152891005747174982241)
            ·
              refine ⟨13395864668254310381236681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17861152891005747174982241 13395864668254310381236681)
              ·
                refine ⟨10046898501190732785927511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395864668254310381236681 10046898501190732785927511)
                ·
                  refine ⟨15070347751786099178891267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046898501190732785927511 15070347751786099178891267)
                  ·
                    refine ⟨22605521627679148768336901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15070347751786099178891267 22605521627679148768336901)
                    ·
                      refine ⟨4238535305189840394063169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22605521627679148768336901 4238535305189840394063169)
                      ·
                        rfl

theorem cell23_8254518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_8254518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254518 prefixEnd_8254518 := by exact prefixLift 8254518
  have htrace : WordTrace (prefixWord ++ tailWord_8254518) baseStart_8254518 baseEnd_8254518 := by
    simpa [prefixWord, tailWord_8254518, baseEnd_8254518] using wordTrace_append hprefix tailTrace_8254518
  have hstable : (prefixWord ++ tailWord_8254518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254518).length < 2 ^ (prefixWord ++ tailWord_8254518).sum := by decide
  have hdescent : baseEnd_8254518 < baseStart_8254518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254521 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_8254521 : Nat := 118140960795 + 8254521 * 2 ^ 59
def prefixEnd_8254521 : Nat := 4983230072969 + 3 ^ 40 * 8254521 * 2
def baseEnd_8254521 : Nat := 4238536845631803882325655

theorem tailTrace_8254521 : CollatzResearch.WordTrace tailWord_8254521 prefixEnd_8254521 4238536845631803882325655 := by
  unfold tailWord_8254521
  simp only [CollatzResearch.WordTrace]
  refine ⟨301067114528287651795187417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200711409685525101196791611 301067114528287651795187417)
  ·
    refine ⟨225800335896215738846390563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301067114528287651795187417 225800335896215738846390563)
    ·
      refine ⟨338700503844323608269585845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225800335896215738846390563 338700503844323608269585845)
      ·
        refine ⟨31753172235405338275273673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338700503844323608269585845 31753172235405338275273673)
        ·
          refine ⟨23814879176554003706455255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31753172235405338275273673 23814879176554003706455255)
          ·
            refine ⟨35722318764831005559682883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23814879176554003706455255 35722318764831005559682883)
            ·
              refine ⟨53583478147246508339524325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35722318764831005559682883 53583478147246508339524325)
              ·
                refine ⟨10046902152608720313660811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53583478147246508339524325 10046902152608720313660811)
                ·
                  refine ⟨15070353228913080470491217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046902152608720313660811 15070353228913080470491217)
                  ·
                    refine ⟨11302764921684810352868413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15070353228913080470491217 11302764921684810352868413)
                    ·
                      refine ⟨4238536845631803882325655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302764921684810352868413 4238536845631803882325655)
                      ·
                        rfl

theorem cell23_8254521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_8254521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254521 prefixEnd_8254521 := by exact prefixLift 8254521
  have htrace : WordTrace (prefixWord ++ tailWord_8254521) baseStart_8254521 baseEnd_8254521 := by
    simpa [prefixWord, tailWord_8254521, baseEnd_8254521] using wordTrace_append hprefix tailTrace_8254521
  have hstable : (prefixWord ++ tailWord_8254521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254521).length < 2 ^ (prefixWord ++ tailWord_8254521).sum := by decide
  have hdescent : baseEnd_8254521 < baseStart_8254521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254524 : List Nat := [2, 2, 2, 2, 2, 2, 4, 7]
def baseStart_8254524 : Nat := 118140960795 + 8254524 * 2 ^ 59
def prefixEnd_8254524 : Nat := 4983230072969 + 3 ^ 40 * 8254524 * 2
def baseEnd_8254524 : Nat := 156982903187917310021783

theorem tailTrace_8254524 : CollatzResearch.WordTrace tailWord_8254524 prefixEnd_8254524 156982903187917310021783 := by
  unfold tailWord_8254524
  simp only [CollatzResearch.WordTrace]
  refine ⟨150533611973638391653773313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200711482631517855538364417 150533611973638391653773313)
  ·
    refine ⟨112900208980228793740329985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150533611973638391653773313 112900208980228793740329985)
    ·
      refine ⟨84675156735171595305247489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112900208980228793740329985 84675156735171595305247489)
      ·
        refine ⟨63506367551378696478935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84675156735171595305247489 63506367551378696478935617)
        ·
          refine ⟨47629775663534022359201713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63506367551378696478935617 47629775663534022359201713)
          ·
            refine ⟨35722331747650516769401285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47629775663534022359201713 35722331747650516769401285)
            ·
              refine ⟨6697937202684471894262741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35722331747650516769401285 6697937202684471894262741)
              ·
                refine ⟨156982903187917310021783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6697937202684471894262741 156982903187917310021783)
                ·
                  rfl

theorem cell23_8254524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 7].length) (baseStart_8254524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254524 prefixEnd_8254524 := by exact prefixLift 8254524
  have htrace : WordTrace (prefixWord ++ tailWord_8254524) baseStart_8254524 baseEnd_8254524 := by
    simpa [prefixWord, tailWord_8254524, baseEnd_8254524] using wordTrace_append hprefix tailTrace_8254524
  have hstable : (prefixWord ++ tailWord_8254524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254524).length < 2 ^ (prefixWord ++ tailWord_8254524).sum := by decide
  have hdescent : baseEnd_8254524 < baseStart_8254524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254535 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_8254535 : Nat := 118140960795 + 8254535 * 2 ^ 59
def prefixEnd_8254535 : Nat := 4983230072969 + 3 ^ 40 * 8254535 * 2
def baseEnd_8254535 : Nat := 4238544034360966827550591

theorem tailTrace_8254535 : CollatzResearch.WordTrace tailWord_8254535 prefixEnd_8254535 4238544034360966827550591 := by
  unfold tailWord_8254535
  simp only [CollatzResearch.WordTrace]
  refine ⟨301067625150236932186197059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200711750100157954790798039 301067625150236932186197059)
  ·
    refine ⟨451601437725355398279295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301067625150236932186197059 451601437725355398279295589)
    ·
      refine ⟨84675269573504137177367923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451601437725355398279295589 84675269573504137177367923)
      ·
        refine ⟨127012904360256205766051885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84675269573504137177367923 127012904360256205766051885)
        ·
          refine ⟨47629839135096077162269457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127012904360256205766051885 47629839135096077162269457)
          ·
            refine ⟨35722379351322057871702093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47629839135096077162269457 35722379351322057871702093)
            ·
              refine ⟨13395892256745771701888285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35722379351322057871702093 13395892256745771701888285)
              ·
                refine ⟨5023459596279664388208107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13395892256745771701888285 5023459596279664388208107)
                ·
                  refine ⟨7535189394419496582312161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023459596279664388208107 7535189394419496582312161)
                  ·
                    refine ⟨5651392045814622436734121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7535189394419496582312161 5651392045814622436734121)
                    ·
                      refine ⟨4238544034360966827550591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651392045814622436734121 4238544034360966827550591)
                      ·
                        rfl

theorem cell23_8254535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_8254535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254535 prefixEnd_8254535 := by exact prefixLift 8254535
  have htrace : WordTrace (prefixWord ++ tailWord_8254535) baseStart_8254535 baseEnd_8254535 := by
    simpa [prefixWord, tailWord_8254535, baseEnd_8254535] using wordTrace_append hprefix tailTrace_8254535
  have hstable : (prefixWord ++ tailWord_8254535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254535).length < 2 ^ (prefixWord ++ tailWord_8254535).sum := by decide
  have hdescent : baseEnd_8254535 < baseStart_8254535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254551 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_8254551 : Nat := 118140960795 + 8254551 * 2 ^ 59
def prefixEnd_8254551 : Nat := 4983230072969 + 3 ^ 40 * 8254551 * 2
def baseEnd_8254551 : Nat := 4238552250051438764950517

theorem tailTrace_8254551 : CollatzResearch.WordTrace tailWord_8254551 prefixEnd_8254551 4238552250051438764950517 := by
  unfold tailWord_8254551
  simp only [CollatzResearch.WordTrace]
  refine ⟨301068208718178966918779507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200712139145452644612519671 301068208718178966918779507)
  ·
    refine ⟨451602313077268450378169261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301068208718178966918779507 451602313077268450378169261)
    ·
      refine ⟨169350867403975668891813473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451602313077268450378169261 169350867403975668891813473)
      ·
        refine ⟨127013150552981751668860105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169350867403975668891813473 127013150552981751668860105)
        ·
          refine ⟨95259862914736313751645079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127013150552981751668860105 95259862914736313751645079)
          ·
            refine ⟨142889794372104470627467619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95259862914736313751645079 142889794372104470627467619)
            ·
              refine ⟨214334691558156705941201429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142889794372104470627467619 214334691558156705941201429)
              ·
                refine ⟨10046938666788595590993817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214334691558156705941201429 10046938666788595590993817)
                ·
                  refine ⟨7535204000091446693245363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046938666788595590993817 7535204000091446693245363)
                  ·
                    refine ⟨11302806000137170039868045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535204000091446693245363 11302806000137170039868045)
                    ·
                      refine ⟨4238552250051438764950517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11302806000137170039868045 4238552250051438764950517)
                      ·
                        rfl

theorem cell23_8254551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_8254551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254551 prefixEnd_8254551 := by exact prefixLift 8254551
  have htrace : WordTrace (prefixWord ++ tailWord_8254551) baseStart_8254551 baseEnd_8254551 := by
    simpa [prefixWord, tailWord_8254551, baseEnd_8254551] using wordTrace_append hprefix tailTrace_8254551
  have hstable : (prefixWord ++ tailWord_8254551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254551).length < 2 ^ (prefixWord ++ tailWord_8254551).sum := by decide
  have hdescent : baseEnd_8254551 < baseStart_8254551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254558 : List Nat := [4, 4, 1, 1, 1, 2, 2, 8]
def baseStart_8254558 : Nat := 118140960795 + 8254558 * 2 ^ 59
def prefixEnd_8254558 : Nat := 4983230072969 + 3 ^ 40 * 8254558 * 2
def baseEnd_8254558 : Nat := 156983549793185934724555

theorem tailTrace_8254558 : CollatzResearch.WordTrace tailWord_8254558 prefixEnd_8254558 156983549793185934724555 := by
  unfold tailWord_8254558
  simp only [CollatzResearch.WordTrace]
  refine ⟨37633558003644200889285541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200712309352769071409522885 37633558003644200889285541)
  ·
    refine ⟨7056292125683287666741039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37633558003644200889285541 7056292125683287666741039)
    ·
      refine ⟨10584438188524931500111559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056292125683287666741039 10584438188524931500111559)
      ·
        refine ⟨15876657282787397250167339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584438188524931500111559 15876657282787397250167339)
        ·
          refine ⟨23814985924181095875251009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876657282787397250167339 23814985924181095875251009)
          ·
            refine ⟨17861239443135821906438257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23814985924181095875251009 17861239443135821906438257)
            ·
              refine ⟨13395929582351866429828693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17861239443135821906438257 13395929582351866429828693)
              ·
                refine ⟨156983549793185934724555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13395929582351866429828693 156983549793185934724555)
                ·
                  rfl

theorem cell23_8254558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_8254558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254558 prefixEnd_8254558 := by exact prefixLift 8254558
  have htrace : WordTrace (prefixWord ++ tailWord_8254558) baseStart_8254558 baseEnd_8254558 := by
    simpa [prefixWord, tailWord_8254558, baseEnd_8254558] using wordTrace_append hprefix tailTrace_8254558
  have hstable : (prefixWord ++ tailWord_8254558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254558).length < 2 ^ (prefixWord ++ tailWord_8254558).sum := by decide
  have hdescent : baseEnd_8254558 < baseStart_8254558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254617 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_8254617 : Nat := 118140960795 + 8254617 * 2 ^ 59
def prefixEnd_8254617 : Nat := 4983230072969 + 3 ^ 40 * 8254617 * 2
def baseEnd_8254617 : Nat := 4238586139774635506725213

theorem tailTrace_8254617 : CollatzResearch.WordTrace tailWord_8254617 prefixEnd_8254617 4238586139774635506725213 := by
  unfold tailWord_8254617
  simp only [CollatzResearch.WordTrace]
  refine ⟨301070615935939860190682105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200713743957293240127121403 301070615935939860190682105)
  ·
    refine ⟨225802961951954895143011579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301070615935939860190682105 225802961951954895143011579)
    ·
      refine ⟨338704442927932342714517369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225802961951954895143011579 338704442927932342714517369)
      ·
        refine ⟨254028332195949257035888027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338704442927932342714517369 254028332195949257035888027)
        ·
          refine ⟨381042498293923885553832041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254028332195949257035888027 381042498293923885553832041)
          ·
            refine ⟨285781873720442914165374031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381042498293923885553832041 285781873720442914165374031)
            ·
              refine ⟨428672810580664371248061047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285781873720442914165374031 428672810580664371248061047)
              ·
                refine ⟨643009215870996556872091571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428672810580664371248061047 643009215870996556872091571)
                ·
                  refine ⟨964513823806494835308137357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643009215870996556872091571 964513823806494835308137357)
                  ·
                    refine ⟨361692683927435563240551509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964513823806494835308137357 361692683927435563240551509)
                    ·
                      refine ⟨4238586139774635506725213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 361692683927435563240551509 4238586139774635506725213)
                      ·
                        rfl

theorem cell23_8254617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_8254617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254617 prefixEnd_8254617 := by exact prefixLift 8254617
  have htrace : WordTrace (prefixWord ++ tailWord_8254617) baseStart_8254617 baseEnd_8254617 := by
    simpa [prefixWord, tailWord_8254617, baseEnd_8254617] using wordTrace_append hprefix tailTrace_8254617
  have hstable : (prefixWord ++ tailWord_8254617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254617).length < 2 ^ (prefixWord ++ tailWord_8254617).sum := by decide
  have hdescent : baseEnd_8254617 < baseStart_8254617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254631 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 7]
def baseStart_8254631 : Nat := 118140960795 + 8254631 * 2 ^ 59
def prefixEnd_8254631 : Nat := 4983230072969 + 3 ^ 40 * 8254631 * 2
def baseEnd_8254631 : Nat := 470954814278199827994461

theorem tailTrace_8254631 : CollatzResearch.WordTrace tailWord_8254631 prefixEnd_8254631 470954814278199827994461 := by
  unfold tailWord_8254631
  simp only [CollatzResearch.WordTrace]
  refine ⟨301071126557889140581691747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200714084371926093721127831 301071126557889140581691747)
  ·
    refine ⟨451606689836833710872537621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301071126557889140581691747 451606689836833710872537621)
    ·
      refine ⟨21169063586101580197150201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 451606689836833710872537621 21169063586101580197150201)
      ·
        refine ⟨15876797689576185147862651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21169063586101580197150201 15876797689576185147862651)
        ·
          refine ⟨23815196534364277721793977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876797689576185147862651 23815196534364277721793977)
          ·
            refine ⟨17861397400773208291345483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23815196534364277721793977 17861397400773208291345483)
            ·
              refine ⟨26792096101159812437018225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17861397400773208291345483 26792096101159812437018225)
              ·
                refine ⟨20094072075869859327763669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26792096101159812437018225 20094072075869859327763669)
                ·
                  refine ⟨470954814278199827994461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20094072075869859327763669 470954814278199827994461)
                  ·
                    rfl

theorem cell23_8254631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 7].length) (baseStart_8254631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254631 prefixEnd_8254631 := by exact prefixLift 8254631
  have htrace : WordTrace (prefixWord ++ tailWord_8254631) baseStart_8254631 baseEnd_8254631 := by
    simpa [prefixWord, tailWord_8254631, baseEnd_8254631] using wordTrace_append hprefix tailTrace_8254631
  have hstable : (prefixWord ++ tailWord_8254631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254631).length < 2 ^ (prefixWord ++ tailWord_8254631).sum := by decide
  have hdescent : baseEnd_8254631 < baseStart_8254631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254646 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_8254646 : Nat := 118140960795 + 8254646 * 2 ^ 59
def prefixEnd_8254646 : Nat := 4983230072969 + 3 ^ 40 * 8254646 * 2
def baseEnd_8254646 : Nat := 4238601030713615893262581

theorem tailTrace_8254646 : CollatzResearch.WordTrace tailWord_8254646 prefixEnd_8254646 4238601030713615893262581 := by
  unfold tailWord_8254646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816979603302174883967987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200714449101889865428991861 18816979603302174883967987)
  ·
    refine ⟨28225469404953262325951981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18816979603302174883967987 28225469404953262325951981)
    ·
      refine ⟨10584551026857473372231993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28225469404953262325951981 10584551026857473372231993)
      ·
        refine ⟨7938413270143105029173995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10584551026857473372231993 7938413270143105029173995)
        ·
          refine ⟨11907619905214657543760993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938413270143105029173995 11907619905214657543760993)
          ·
            refine ⟨8930714928910993157820745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11907619905214657543760993 8930714928910993157820745)
            ·
              refine ⟨6698036196683244868365559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8930714928910993157820745 6698036196683244868365559)
              ·
                refine ⟨10047054295024867302548339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698036196683244868365559 10047054295024867302548339)
                ·
                  refine ⟨15070581442537300953822509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047054295024867302548339 15070581442537300953822509)
                  ·
                    refine ⟨5651468040951487857683441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15070581442537300953822509 5651468040951487857683441)
                    ·
                      refine ⟨4238601030713615893262581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651468040951487857683441 4238601030713615893262581)
                      ·
                        rfl

theorem cell23_8254646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_8254646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254646 prefixEnd_8254646 := by exact prefixLift 8254646
  have htrace : WordTrace (prefixWord ++ tailWord_8254646) baseStart_8254646 baseEnd_8254646 := by
    simpa [prefixWord, tailWord_8254646, baseEnd_8254646] using wordTrace_append hprefix tailTrace_8254646
  have hstable : (prefixWord ++ tailWord_8254646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254646).length < 2 ^ (prefixWord ++ tailWord_8254646).sum := by decide
  have hdescent : baseEnd_8254646 < baseStart_8254646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254718 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_8254718 : Nat := 118140960795 + 8254718 * 2 ^ 59
def prefixEnd_8254718 : Nat := 4983230072969 + 3 ^ 40 * 8254718 * 2
def baseEnd_8254718 : Nat := 4238638001320739611562249

theorem tailTrace_8254718 : CollatzResearch.WordTrace tailWord_8254718 prefixEnd_8254718 4238638001320739611562249 := by
  unfold tailWord_8254718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634287463571744305013601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200716199805715969626739205 37634287463571744305013601)
  ·
    refine ⟨28225715597678808228760201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37634287463571744305013601 28225715597678808228760201)
    ·
      refine ⟨21169286698259106171570151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28225715597678808228760201 21169286698259106171570151)
      ·
        refine ⟨31753930047388659257355227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21169286698259106171570151 31753930047388659257355227)
        ·
          refine ⟨47630895071082988886032841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31753930047388659257355227 47630895071082988886032841)
          ·
            refine ⟨35723171303312241664524631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47630895071082988886032841 35723171303312241664524631)
            ·
              refine ⟨53584756954968362496786947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35723171303312241664524631 53584756954968362496786947)
              ·
                refine ⟨80377135432452543745180421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53584756954968362496786947 80377135432452543745180421)
                ·
                  refine ⟨15070712893584851952221329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80377135432452543745180421 15070712893584851952221329)
                  ·
                    refine ⟨11303034670188638964165997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15070712893584851952221329 11303034670188638964165997)
                    ·
                      refine ⟨4238638001320739611562249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303034670188638964165997 4238638001320739611562249)
                      ·
                        rfl

theorem cell23_8254718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_8254718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254718 prefixEnd_8254718 := by exact prefixLift 8254718
  have htrace : WordTrace (prefixWord ++ tailWord_8254718) baseStart_8254718 baseEnd_8254718 := by
    simpa [prefixWord, tailWord_8254718, baseEnd_8254718] using wordTrace_append hprefix tailTrace_8254718
  have hstable : (prefixWord ++ tailWord_8254718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254718).length < 2 ^ (prefixWord ++ tailWord_8254718).sum := by decide
  have hdescent : baseEnd_8254718 < baseStart_8254718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254725 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_8254725 : Nat := 118140960795 + 8254725 * 2 ^ 59
def prefixEnd_8254725 : Nat := 4983230072969 + 3 ^ 40 * 8254725 * 2
def baseEnd_8254725 : Nat := 1412880531895107028058239

theorem tailTrace_8254725 : CollatzResearch.WordTrace tailWord_8254725 prefixEnd_8254725 1412880531895107028058239 := by
  unfold tailWord_8254725
  simp only [CollatzResearch.WordTrace]
  refine ⟨301074555019548594635613629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200716370013032396423742419 301074555019548594635613629)
  ·
    refine ⟨112902958132330722988355111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301074555019548594635613629 112902958132330722988355111)
    ·
      refine ⟨169354437198496084482532667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112902958132330722988355111 169354437198496084482532667)
      ·
        refine ⟨254031655797744126723799001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169354437198496084482532667 254031655797744126723799001)
        ·
          refine ⟨190523741848308095042849251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254031655797744126723799001 190523741848308095042849251)
          ·
            refine ⟨285785612772462142564273877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190523741848308095042849251 285785612772462142564273877)
            ·
              refine ⟨6698100299354581466350169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285785612772462142564273877 6698100299354581466350169)
              ·
                refine ⟨5023575224515936099762627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6698100299354581466350169 5023575224515936099762627)
                ·
                  refine ⟨7535362836773904149643941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023575224515936099762627 7535362836773904149643941)
                  ·
                    refine ⟨1412880531895107028058239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535362836773904149643941 1412880531895107028058239)
                    ·
                      rfl

theorem cell23_8254725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_8254725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254725 prefixEnd_8254725 := by exact prefixLift 8254725
  have htrace : WordTrace (prefixWord ++ tailWord_8254725) baseStart_8254725 baseEnd_8254725 := by
    simpa [prefixWord, tailWord_8254725, baseEnd_8254725] using wordTrace_append hprefix tailTrace_8254725
  have hstable : (prefixWord ++ tailWord_8254725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254725).length < 2 ^ (prefixWord ++ tailWord_8254725).sum := by decide
  have hdescent : baseEnd_8254725 < baseStart_8254725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254748 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_8254748 : Nat := 118140960795 + 8254748 * 2 ^ 59
def prefixEnd_8254748 : Nat := 4983230072969 + 3 ^ 40 * 8254748 * 2
def baseEnd_8254748 : Nat := 4238653405740374494187111

theorem tailTrace_8254748 : CollatzResearch.WordTrace tailWord_8254748 prefixEnd_8254748 4238653405740374494187111 := by
  unfold tailWord_8254748
  simp only [CollatzResearch.WordTrace]
  refine ⟨150537696949232634781850449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200716929265643513042467265 150537696949232634781850449)
  ·
    refine ⟨112903272711924476086387837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150537696949232634781850449 112903272711924476086387837)
    ·
      refine ⟨42338727266971678532395439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112903272711924476086387837 42338727266971678532395439)
      ·
        refine ⟨63508090900457517798593159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42338727266971678532395439 63508090900457517798593159)
        ·
          refine ⟨95262136350686276697889739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63508090900457517798593159 95262136350686276697889739)
          ·
            refine ⟨142893204526029415046834609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95262136350686276697889739 142893204526029415046834609)
            ·
              refine ⟨107169903394522061285125957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142893204526029415046834609 107169903394522061285125957)
              ·
                refine ⟨20094356886472886490961117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107169903394522061285125957 20094356886472886490961117)
                ·
                  refine ⟨7535383832427332434110419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20094356886472886490961117 7535383832427332434110419)
                  ·
                    refine ⟨11303075748640998651165629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535383832427332434110419 11303075748640998651165629)
                    ·
                      refine ⟨4238653405740374494187111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303075748640998651165629 4238653405740374494187111)
                      ·
                        rfl

theorem cell23_8254748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_8254748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254748 prefixEnd_8254748 := by exact prefixLift 8254748
  have htrace : WordTrace (prefixWord ++ tailWord_8254748) baseStart_8254748 baseEnd_8254748 := by
    simpa [prefixWord, tailWord_8254748, baseEnd_8254748] using wordTrace_append hprefix tailTrace_8254748
  have hstable : (prefixWord ++ tailWord_8254748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254748).length < 2 ^ (prefixWord ++ tailWord_8254748).sum := by decide
  have hdescent : baseEnd_8254748 < baseStart_8254748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254768 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_8254768 : Nat := 118140960795 + 8254768 * 2 ^ 59
def prefixEnd_8254768 : Nat := 4983230072969 + 3 ^ 40 * 8254768 * 2
def baseEnd_8254768 : Nat := 1412887891784488138645673

theorem tailTrace_8254768 : CollatzResearch.WordTrace tailWord_8254768 prefixEnd_8254768 1412887891784488138645673 := by
  unfold tailWord_8254768
  simp only [CollatzResearch.WordTrace]
  refine ⟨150538061679196406489714479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200717415572261875319619305 150538061679196406489714479)
  ·
    refine ⟨225807092518794609734571719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150538061679196406489714479 225807092518794609734571719)
    ·
      refine ⟨338710638778191914601857579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225807092518794609734571719 338710638778191914601857579)
      ·
        refine ⟨508065958167287871902786369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338710638778191914601857579 508065958167287871902786369)
        ·
          refine ⟨381049468625465903927089777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508065958167287871902786369 381049468625465903927089777)
          ·
            refine ⟨285787101469099427945317333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381049468625465903927089777 285787101469099427945317333)
            ·
              refine ⟨6698135190682017842468375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285787101469099427945317333 6698135190682017842468375)
              ·
                refine ⟨10047202786023026763702563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698135190682017842468375 10047202786023026763702563)
                ·
                  refine ⟨15070804179034540145553845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047202786023026763702563 15070804179034540145553845)
                  ·
                    refine ⟨1412887891784488138645673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15070804179034540145553845 1412887891784488138645673)
                    ·
                      rfl

theorem cell23_8254768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_8254768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254768 prefixEnd_8254768 := by exact prefixLift 8254768
  have htrace : WordTrace (prefixWord ++ tailWord_8254768) baseStart_8254768 baseEnd_8254768 := by
    simpa [prefixWord, tailWord_8254768, baseEnd_8254768] using wordTrace_append hprefix tailTrace_8254768
  have hstable : (prefixWord ++ tailWord_8254768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254768).length < 2 ^ (prefixWord ++ tailWord_8254768).sum := by decide
  have hdescent : baseEnd_8254768 < baseStart_8254768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254782 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_8254782 : Nat := 118140960795 + 8254782 * 2 ^ 59
def prefixEnd_8254782 : Nat := 4983230072969 + 3 ^ 40 * 8254782 * 2
def baseEnd_8254782 : Nat := 4238670864082627361161955

theorem tailTrace_8254782 : CollatzResearch.WordTrace tailWord_8254782 prefixEnd_8254782 4238670864082627361161955 := by
  unfold tailWord_8254782
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634579247542761671304825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200717755986894728913625733 37634579247542761671304825)
  ·
    refine ⟨28225934435657071253478619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37634579247542761671304825 28225934435657071253478619)
    ·
      refine ⟨42338901653485606880217929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28225934435657071253478619 42338901653485606880217929)
      ·
        refine ⟨31754176240114205160163447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42338901653485606880217929 31754176240114205160163447)
        ·
          refine ⟨47631264360171307740245171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31754176240114205160163447 47631264360171307740245171)
          ·
            refine ⟨71446896540256961610367757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47631264360171307740245171 71446896540256961610367757)
            ·
              refine ⟨26792586202596360603887909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71446896540256961610367757 26792586202596360603887909)
              ·
                refine ⟨5023609912986817613228983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26792586202596360603887909 5023609912986817613228983)
                ·
                  refine ⟨7535414869480226419843475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023609912986817613228983 7535414869480226419843475)
                  ·
                    refine ⟨11303122304220339629765213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535414869480226419843475 11303122304220339629765213)
                    ·
                      refine ⟨4238670864082627361161955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303122304220339629765213 4238670864082627361161955)
                      ·
                        rfl

theorem cell23_8254782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_8254782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254782 prefixEnd_8254782 := by exact prefixLift 8254782
  have htrace : WordTrace (prefixWord ++ tailWord_8254782) baseStart_8254782 baseEnd_8254782 := by
    simpa [prefixWord, tailWord_8254782, baseEnd_8254782] using wordTrace_append hprefix tailTrace_8254782
  have hstable : (prefixWord ++ tailWord_8254782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254782).length < 2 ^ (prefixWord ++ tailWord_8254782).sum := by decide
  have hdescent : baseEnd_8254782 < baseStart_8254782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254798 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_8254798 : Nat := 118140960795 + 8254798 * 2 ^ 59
def prefixEnd_8254798 : Nat := 4983230072969 + 3 ^ 40 * 8254798 * 2
def baseEnd_8254798 : Nat := 1412893026591033099520627

theorem tailTrace_8254798 : CollatzResearch.WordTrace tailWord_8254798 prefixEnd_8254798 1412893026591033099520627 := by
  unfold tailWord_8254798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634652193535516012877631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200718145032189418735347365 37634652193535516012877631)
  ·
    refine ⟨56451978290303274019316447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37634652193535516012877631 56451978290303274019316447)
    ·
      refine ⟨84677967435454911028974671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56451978290303274019316447 84677967435454911028974671)
      ·
        refine ⟨127016951153182366543462007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84677967435454911028974671 127016951153182366543462007)
        ·
          refine ⟨190525426729773549815193011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127016951153182366543462007 190525426729773549815193011)
          ·
            refine ⟨285788140094660324722789517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190525426729773549815193011 285788140094660324722789517)
            ·
              refine ⟨107170552535497621771046069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285788140094660324722789517 107170552535497621771046069)
              ·
                refine ⟨10047239300202902041035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107170552535497621771046069 10047239300202902041035569)
                ·
                  refine ⟨7535429475152176530776677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10047239300202902041035569 7535429475152176530776677)
                  ·
                    refine ⟨1412893026591033099520627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535429475152176530776677 1412893026591033099520627)
                    ·
                      rfl

theorem cell23_8254798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_8254798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254798 prefixEnd_8254798 := by exact prefixLift 8254798
  have htrace : WordTrace (prefixWord ++ tailWord_8254798) baseStart_8254798 baseEnd_8254798 := by
    simpa [prefixWord, tailWord_8254798, baseEnd_8254798] using wordTrace_append hprefix tailTrace_8254798
  have hstable : (prefixWord ++ tailWord_8254798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254798).length < 2 ^ (prefixWord ++ tailWord_8254798).sum := by decide
  have hdescent : baseEnd_8254798 < baseStart_8254798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254805 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_8254805 : Nat := 118140960795 + 8254805 * 2 ^ 59
def prefixEnd_8254805 : Nat := 4983230072969 + 3 ^ 40 * 8254805 * 2
def baseEnd_8254805 : Nat := 4238682674137680771174349

theorem tailTrace_8254805 : CollatzResearch.WordTrace tailWord_8254805 prefixEnd_8254805 4238682674137680771174349 := by
  unfold tailWord_8254805
  simp only [CollatzResearch.WordTrace]
  refine ⟨301077472859258768298525869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200718315239505845532350579 301077472859258768298525869)
  ·
    refine ⟨112904052322222038111947201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301077472859258768298525869 112904052322222038111947201)
    ·
      refine ⟨84678039241666528583960401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112904052322222038111947201 84678039241666528583960401)
      ·
        refine ⟨63508529431249896437970301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84678039241666528583960401 63508529431249896437970301)
        ·
          refine ⟨23815698536718711164238863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63508529431249896437970301 23815698536718711164238863)
          ·
            refine ⟨35723547805078066746358295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23815698536718711164238863 35723547805078066746358295)
            ·
              refine ⟨53585321707617100119537443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35723547805078066746358295 53585321707617100119537443)
              ·
                refine ⟨80377982561425650179306165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53585321707617100119537443 80377982561425650179306165)
                ·
                  refine ⟨7535435865133654704309953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80377982561425650179306165 7535435865133654704309953)
                  ·
                    refine ⟨5651576898850241028232465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7535435865133654704309953 5651576898850241028232465)
                    ·
                      refine ⟨4238682674137680771174349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651576898850241028232465 4238682674137680771174349)
                      ·
                        rfl

theorem cell23_8254805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_8254805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254805 prefixEnd_8254805 := by exact prefixLift 8254805
  have htrace : WordTrace (prefixWord ++ tailWord_8254805) baseStart_8254805 baseEnd_8254805 := by
    simpa [prefixWord, tailWord_8254805, baseEnd_8254805] using wordTrace_append hprefix tailTrace_8254805
  have hstable : (prefixWord ++ tailWord_8254805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254805).length < 2 ^ (prefixWord ++ tailWord_8254805).sum := by decide
  have hdescent : baseEnd_8254805 < baseStart_8254805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254808 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_8254808 : Nat := 118140960795 + 8254808 * 2 ^ 59
def prefixEnd_8254808 : Nat := 4983230072969 + 3 ^ 40 * 8254808 * 2
def baseEnd_8254808 : Nat := 4238684214579644259436835

theorem tailTrace_8254808 : CollatzResearch.WordTrace tailWord_8254808 prefixEnd_8254808 4238684214579644259436835 := by
  unfold tailWord_8254808
  simp only [CollatzResearch.WordTrace]
  refine ⟨150538791139123949905442539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200718388185498599873923385 150538791139123949905442539)
  ·
    refine ⟨225808186708685924858163809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150538791139123949905442539 225808186708685924858163809)
    ·
      refine ⟨169356140031514443643622857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225808186708685924858163809 169356140031514443643622857)
      ·
        refine ⟨127017105023635832732717143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169356140031514443643622857 127017105023635832732717143)
        ·
          refine ⟨190525657535453749099075715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127017105023635832732717143 190525657535453749099075715)
          ·
            refine ⟨285788486303180623648613573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190525657535453749099075715 285788486303180623648613573)
            ·
              refine ⟨53585341181846366934115045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285788486303180623648613573 53585341181846366934115045)
              ·
                refine ⟨10047251471596193800146571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53585341181846366934115045 10047251471596193800146571)
                ·
                  refine ⟨15070877207394290700219857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047251471596193800146571 15070877207394290700219857)
                  ·
                    refine ⟨11303157905545718025164893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15070877207394290700219857 11303157905545718025164893)
                    ·
                      refine ⟨4238684214579644259436835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303157905545718025164893 4238684214579644259436835)
                      ·
                        rfl

theorem cell23_8254808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_8254808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254808 prefixEnd_8254808 := by exact prefixLift 8254808
  have htrace : WordTrace (prefixWord ++ tailWord_8254808) baseStart_8254808 baseEnd_8254808 := by
    simpa [prefixWord, tailWord_8254808, baseEnd_8254808] using wordTrace_append hprefix tailTrace_8254808
  have hstable : (prefixWord ++ tailWord_8254808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254808).length < 2 ^ (prefixWord ++ tailWord_8254808).sum := by decide
  have hdescent : baseEnd_8254808 < baseStart_8254808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254818 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_8254818 : Nat := 118140960795 + 8254818 * 2 ^ 59
def prefixEnd_8254818 : Nat := 4983230072969 + 3 ^ 40 * 8254818 * 2
def baseEnd_8254818 : Nat := 4238689349386189220311789

theorem tailTrace_8254818 : CollatzResearch.WordTrace tailWord_8254818 prefixEnd_8254818 4238689349386189220311789 := by
  unfold tailWord_8254818
  simp only [CollatzResearch.WordTrace]
  refine ⟨75269486752052917879687277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200718631338807781012499405 75269486752052917879687277)
  ·
    refine ⟨28226057532019844204882729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75269486752052917879687277 28226057532019844204882729)
    ·
      refine ⟨21169543149014883153662047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28226057532019844204882729 21169543149014883153662047)
      ·
        refine ⟨31754314723522324730493071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21169543149014883153662047 31754314723522324730493071)
        ·
          refine ⟨47631472085283487095739607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31754314723522324730493071 47631472085283487095739607)
          ·
            refine ⟨71447208127925230643609411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47631472085283487095739607 71447208127925230643609411)
            ·
              refine ⟨107170812191887845965414117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71447208127925230643609411 107170812191887845965414117)
              ·
                refine ⟨20094527285978971118515147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107170812191887845965414117 20094527285978971118515147)
                ·
                  refine ⟨30141790928968456677772721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20094527285978971118515147 30141790928968456677772721)
                  ·
                    refine ⟨22606343196726342508329541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30141790928968456677772721 22606343196726342508329541)
                    ·
                      refine ⟨4238689349386189220311789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22606343196726342508329541 4238689349386189220311789)
                      ·
                        rfl

theorem cell23_8254818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_8254818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254818 prefixEnd_8254818 := by exact prefixLift 8254818
  have htrace : WordTrace (prefixWord ++ tailWord_8254818) baseStart_8254818 baseEnd_8254818 := by
    simpa [prefixWord, tailWord_8254818, baseEnd_8254818] using wordTrace_append hprefix tailTrace_8254818
  have hstable : (prefixWord ++ tailWord_8254818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254818).length < 2 ^ (prefixWord ++ tailWord_8254818).sum := by decide
  have hdescent : baseEnd_8254818 < baseStart_8254818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2]
def baseStart_8254848 : Nat := 118140960795 + 8254848 * 2 ^ 59
def prefixEnd_8254848 : Nat := 4983230072969 + 3 ^ 40 * 8254848 * 2
def baseEnd_8254848 : Nat := 4238704753805824102936651

theorem tailTrace_8254848 : CollatzResearch.WordTrace tailWord_8254848 prefixEnd_8254848 4238704753805824102936651 := by
  unfold tailWord_8254848
  simp only [CollatzResearch.WordTrace]
  refine ⟨150539520599051493321170599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200719360798735324428227465 150539520599051493321170599)
  ·
    refine ⟨225809280898577239981755899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150539520599051493321170599 225809280898577239981755899)
    ·
      refine ⟨338713921347865859972633849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225809280898577239981755899 338713921347865859972633849)
      ·
        refine ⟨254035441010899394979475387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338713921347865859972633849 254035441010899394979475387)
        ·
          refine ⟨381053161516349092469213081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254035441010899394979475387 381053161516349092469213081)
          ·
            refine ⟨285789871137261819351909811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381053161516349092469213081 285789871137261819351909811)
            ·
              refine ⟨428684806705892729027864717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285789871137261819351909811 428684806705892729027864717)
              ·
                refine ⟨160756802514709773385449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428684806705892729027864717 160756802514709773385449269)
                ·
                  refine ⟨15070950235754041254885869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160756802514709773385449269 15070950235754041254885869)
                  ·
                    refine ⟨5651606338407765470582201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15070950235754041254885869 5651606338407765470582201)
                    ·
                      refine ⟨4238704753805824102936651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651606338407765470582201 4238704753805824102936651)
                      ·
                        rfl

theorem cell23_8254848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_8254848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254848 prefixEnd_8254848 := by exact prefixLift 8254848
  have htrace : WordTrace (prefixWord ++ tailWord_8254848) baseStart_8254848 baseEnd_8254848 := by
    simpa [prefixWord, tailWord_8254848, baseEnd_8254848] using wordTrace_append hprefix tailTrace_8254848
  have hstable : (prefixWord ++ tailWord_8254848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254848).length < 2 ^ (prefixWord ++ tailWord_8254848).sum := by decide
  have hdescent : baseEnd_8254848 < baseStart_8254848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254855 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_8254855 : Nat := 118140960795 + 8254855 * 2 ^ 59
def prefixEnd_8254855 : Nat := 4983230072969 + 3 ^ 40 * 8254855 * 2
def baseEnd_8254855 : Nat := 4238708348170405575549119

theorem tailTrace_8254855 : CollatzResearch.WordTrace tailWord_8254855 prefixEnd_8254855 4238708348170405575549119 := by
  unfold tailWord_8254855
  simp only [CollatzResearch.WordTrace]
  refine ⟨301079296509077626837846019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200719531006051751225230679 301079296509077626837846019)
  ·
    refine ⟨451618944763616440256769029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301079296509077626837846019 451618944763616440256769029)
    ·
      refine ⟨84678552143178082548144193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451618944763616440256769029 84678552143178082548144193)
      ·
        refine ⟨63508914107383561911108145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84678552143178082548144193 63508914107383561911108145)
        ·
          refine ⟨47631685580537671433331109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63508914107383561911108145 47631685580537671433331109)
          ·
            refine ⟨8930941046350813393749583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47631685580537671433331109 8930941046350813393749583)
            ·
              refine ⟨13396411569526220090624375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930941046350813393749583 13396411569526220090624375)
              ·
                refine ⟨20094617354289330135936563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13396411569526220090624375 20094617354289330135936563)
                ·
                  refine ⟨30141926031433995203904845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20094617354289330135936563 30141926031433995203904845)
                  ·
                    refine ⟨11303222261787748201464317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30141926031433995203904845 11303222261787748201464317)
                    ·
                      refine ⟨4238708348170405575549119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303222261787748201464317 4238708348170405575549119)
                      ·
                        rfl

theorem cell23_8254855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_8254855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254855 prefixEnd_8254855 := by exact prefixLift 8254855
  have htrace : WordTrace (prefixWord ++ tailWord_8254855) baseStart_8254855 baseEnd_8254855 := by
    simpa [prefixWord, tailWord_8254855, baseEnd_8254855] using wordTrace_append hprefix tailTrace_8254855
  have hstable : (prefixWord ++ tailWord_8254855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254855).length < 2 ^ (prefixWord ++ tailWord_8254855).sum := by decide
  have hdescent : baseEnd_8254855 < baseStart_8254855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254862 : List Nat := [4, 1, 1, 4, 3, 1, 2, 7]
def baseStart_8254862 : Nat := 118140960795 + 8254862 * 2 ^ 59
def prefixEnd_8254862 : Nat := 4983230072969 + 3 ^ 40 * 8254862 * 2
def baseEnd_8254862 : Nat := 156989331204999520302281

theorem tailTrace_8254862 : CollatzResearch.WordTrace tailWord_8254862 prefixEnd_8254862 156989331204999520302281 := by
  unfold tailWord_8254862
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634943977506533379168855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200719701213368178022233893 37634943977506533379168855)
  ·
    refine ⟨56452415966259800068753283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37634943977506533379168855 56452415966259800068753283)
    ·
      refine ⟨84678623949389700103129925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56452415966259800068753283 84678623949389700103129925)
      ·
        refine ⟨15877241990510568769336861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84678623949389700103129925 15877241990510568769336861)
        ·
          refine ⟨5953965746441463288501323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15877241990510568769336861 5953965746441463288501323)
          ·
            refine ⟨8930948619662194932751985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953965746441463288501323 8930948619662194932751985)
            ·
              refine ⟨6698211464746646199563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8930948619662194932751985 6698211464746646199563989)
              ·
                refine ⟨156989331204999520302281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6698211464746646199563989 156989331204999520302281)
                ·
                  rfl

theorem cell23_8254862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_8254862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254862 prefixEnd_8254862 := by exact prefixLift 8254862
  have htrace : WordTrace (prefixWord ++ tailWord_8254862) baseStart_8254862 baseEnd_8254862 := by
    simpa [prefixWord, tailWord_8254862, baseEnd_8254862] using wordTrace_append hprefix tailTrace_8254862
  have hstable : (prefixWord ++ tailWord_8254862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254862).length < 2 ^ (prefixWord ++ tailWord_8254862).sum := by decide
  have hdescent : baseEnd_8254862 < baseStart_8254862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254868 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_8254868 : Nat := 118140960795 + 8254868 * 2 ^ 59
def prefixEnd_8254868 : Nat := 4983230072969 + 3 ^ 40 * 8254868 * 2
def baseEnd_8254868 : Nat := 4238715023418914024686559

theorem tailTrace_8254868 : CollatzResearch.WordTrace tailWord_8254868 prefixEnd_8254868 4238715023418914024686559 := by
  unfold tailWord_8254868
  simp only [CollatzResearch.WordTrace]
  refine ⟨150539885329015265029034629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200719847105353686705379505 150539885329015265029034629)
  ·
    refine ⟨28226228499190362192943993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150539885329015265029034629 28226228499190362192943993)
    ·
      refine ⟨21169671374392771644707995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28226228499190362192943993 21169671374392771644707995)
      ·
        refine ⟨31754507061589157467061993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21169671374392771644707995 31754507061589157467061993)
        ·
          refine ⟨23815880296191868100296495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31754507061589157467061993 23815880296191868100296495)
          ·
            refine ⟨35723820444287802150444743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23815880296191868100296495 35723820444287802150444743)
            ·
              refine ⟨53585730666431703225667115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35723820444287802150444743 53585730666431703225667115)
              ·
                refine ⟨80378595999647554838500673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53585730666431703225667115 80378595999647554838500673)
                ·
                  refine ⟨60283946999735666128875505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80378595999647554838500673 60283946999735666128875505)
                  ·
                    refine ⟨45212960249801749596656629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60283946999735666128875505 45212960249801749596656629)
                    ·
                      refine ⟨4238715023418914024686559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45212960249801749596656629 4238715023418914024686559)
                      ·
                        rfl

theorem cell23_8254868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_8254868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254868 prefixEnd_8254868 := by exact prefixLift 8254868
  have htrace : WordTrace (prefixWord ++ tailWord_8254868) baseStart_8254868 baseEnd_8254868 := by
    simpa [prefixWord, tailWord_8254868, baseEnd_8254868] using wordTrace_append hprefix tailTrace_8254868
  have hstable : (prefixWord ++ tailWord_8254868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254868).length < 2 ^ (prefixWord ++ tailWord_8254868).sum := by decide
  have hdescent : baseEnd_8254868 < baseStart_8254868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254882 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_8254882 : Nat := 118140960795 + 8254882 * 2 ^ 59
def prefixEnd_8254882 : Nat := 4983230072969 + 3 ^ 40 * 8254882 * 2
def baseEnd_8254882 : Nat := 4238722212148076969911495

theorem tailTrace_8254882 : CollatzResearch.WordTrace tailWord_8254882 prefixEnd_8254882 4238722212148076969911495 := by
  unfold tailWord_8254882
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270070319994952612269725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200720187519986540299385933 75270070319994952612269725)
  ·
    refine ⟨28226276369998107229601147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75270070319994952612269725 28226276369998107229601147)
    ·
      refine ⟨42339414554997160844401721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28226276369998107229601147 42339414554997160844401721)
      ·
        refine ⟨31754560916247870633301291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42339414554997160844401721 31754560916247870633301291)
        ·
          refine ⟨47631841374371805949951937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31754560916247870633301291 47631841374371805949951937)
          ·
            refine ⟨35723881030778854462463953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47631841374371805949951937 35723881030778854462463953)
            ·
              refine ⟨26792910773084140846847965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35723881030778854462463953 26792910773084140846847965)
              ·
                refine ⟨10047341539906552817567987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26792910773084140846847965 10047341539906552817567987)
                ·
                  refine ⟨15071012309859829226351981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047341539906552817567987 15071012309859829226351981)
                  ·
                    refine ⟨5651629616197435959881993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15071012309859829226351981 5651629616197435959881993)
                    ·
                      refine ⟨4238722212148076969911495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651629616197435959881993 4238722212148076969911495)
                      ·
                        rfl

theorem cell23_8254882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_8254882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254882 prefixEnd_8254882 := by exact prefixLift 8254882
  have htrace : WordTrace (prefixWord ++ tailWord_8254882) baseStart_8254882 baseEnd_8254882 := by
    simpa [prefixWord, tailWord_8254882, baseEnd_8254882] using wordTrace_append hprefix tailTrace_8254882
  have hstable : (prefixWord ++ tailWord_8254882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254882).length < 2 ^ (prefixWord ++ tailWord_8254882).sum := by decide
  have hdescent : baseEnd_8254882 < baseStart_8254882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254958 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_8254958 : Nat := 118140960795 + 8254958 * 2 ^ 59
def prefixEnd_8254958 : Nat := 4983230072969 + 3 ^ 40 * 8254958 * 2
def baseEnd_8254958 : Nat := 4238761236677818672561145

theorem tailTrace_8254958 : CollatzResearch.WordTrace tailWord_8254958 prefixEnd_8254958 4238761236677818672561145 := by
  unfold tailWord_8254958
  simp only [CollatzResearch.WordTrace]
  refine ⟨37635381653463059428605691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200722035485136316952563685 37635381653463059428605691)
  ·
    refine ⟨56453072480194589142908537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37635381653463059428605691 56453072480194589142908537)
    ·
      refine ⟨42339804360145941857181403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56453072480194589142908537 42339804360145941857181403)
      ·
        refine ⟨63509706540218912785772105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42339804360145941857181403 63509706540218912785772105)
        ·
          refine ⟨47632279905164184589329079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63509706540218912785772105 47632279905164184589329079)
          ·
            refine ⟨71448419857746276883993619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47632279905164184589329079 71448419857746276883993619)
            ·
              refine ⟨107172629786619415325990429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71448419857746276883993619 107172629786619415325990429)
              ·
                refine ⟨40189736169982280747246411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107172629786619415325990429 40189736169982280747246411)
                ·
                  refine ⟨60284604254973421120869617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40189736169982280747246411 60284604254973421120869617)
                  ·
                    refine ⟨45213453191230065840652213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60284604254973421120869617 45213453191230065840652213)
                    ·
                      refine ⟨4238761236677818672561145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45213453191230065840652213 4238761236677818672561145)
                      ·
                        rfl

theorem cell23_8254958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_8254958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254958 prefixEnd_8254958 := by exact prefixLift 8254958
  have htrace : WordTrace (prefixWord ++ tailWord_8254958) baseStart_8254958 baseEnd_8254958 := by
    simpa [prefixWord, tailWord_8254958, baseEnd_8254958] using wordTrace_append hprefix tailTrace_8254958
  have hstable : (prefixWord ++ tailWord_8254958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254958).length < 2 ^ (prefixWord ++ tailWord_8254958).sum := by decide
  have hdescent : baseEnd_8254958 < baseStart_8254958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254971 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_8254971 : Nat := 118140960795 + 8254971 * 2 ^ 59
def prefixEnd_8254971 : Nat := 4983230072969 + 3 ^ 40 * 8254971 * 2
def baseEnd_8254971 : Nat := 4238767911926327121698585

theorem tailTrace_8254971 : CollatzResearch.WordTrace tailWord_8254971 prefixEnd_8254971 4238767911926327121698585 := by
  unfold tailWord_8254971
  simp only [CollatzResearch.WordTrace]
  refine ⟨301083527376657378649068767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200722351584438252432712511 301083527376657378649068767)
  ·
    refine ⟨451625291064986067973603151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301083527376657378649068767 451625291064986067973603151)
    ·
      refine ⟨677437936597479101960404727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451625291064986067973603151 677437936597479101960404727)
      ·
        refine ⟨1016156904896218652940607091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677437936597479101960404727 1016156904896218652940607091)
        ·
          refine ⟨1524235357344327979410910637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016156904896218652940607091 1524235357344327979410910637)
          ·
            refine ⟨571588259004122992279091489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1524235357344327979410910637 571588259004122992279091489)
            ·
              refine ⟨428691194253092244209318617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571588259004122992279091489 428691194253092244209318617)
              ·
                refine ⟨321518395689819183156988963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428691194253092244209318617 321518395689819183156988963)
                ·
                  refine ⟨482277593534728774735483445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321518395689819183156988963 482277593534728774735483445)
                  ·
                    refine ⟨45213524393880822631451573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 482277593534728774735483445 45213524393880822631451573)
                    ·
                      refine ⟨4238767911926327121698585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45213524393880822631451573 4238767911926327121698585)
                      ·
                        rfl

theorem cell23_8254971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_8254971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8254971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8254971 prefixEnd_8254971 := by exact prefixLift 8254971
  have htrace : WordTrace (prefixWord ++ tailWord_8254971) baseStart_8254971 baseEnd_8254971 := by
    simpa [prefixWord, tailWord_8254971, baseEnd_8254971] using wordTrace_append hprefix tailTrace_8254971
  have hstable : (prefixWord ++ tailWord_8254971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254971).length < 2 ^ (prefixWord ++ tailWord_8254971).sum := by decide
  have hdescent : baseEnd_8254971 < baseStart_8254971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255005 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_8255005 : Nat := 118140960795 + 8255005 * 2 ^ 59
def prefixEnd_8255005 : Nat := 4983230072969 + 3 ^ 40 * 8255005 * 2
def baseEnd_8255005 : Nat := 4238785370268579988673429

theorem tailTrace_8255005 : CollatzResearch.WordTrace tailWord_8255005 prefixEnd_8255005 4238785370268579988673429 := by
  unfold tailWord_8255005
  simp only [CollatzResearch.WordTrace]
  refine ⟨301084767458534202455806469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200723178305689468303870979 301084767458534202455806469)
  ·
    refine ⟨56453393898475162960463713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301084767458534202455806469 56453393898475162960463713)
    ·
      refine ⟨42340045423856372220347785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56453393898475162960463713 42340045423856372220347785)
      ·
        refine ⟨31755034067892279165260839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42340045423856372220347785 31755034067892279165260839)
        ·
          refine ⟨47632551101838418747891259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31755034067892279165260839 47632551101838418747891259)
          ·
            refine ⟨71448826652757628121836889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47632551101838418747891259 71448826652757628121836889)
            ·
              refine ⟨53586619989568221091377667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71448826652757628121836889 53586619989568221091377667)
              ·
                refine ⟨80379929984352331637066501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53586619989568221091377667 80379929984352331637066501)
                ·
                  refine ⟨15071236872066062181949969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80379929984352331637066501 15071236872066062181949969)
                  ·
                    refine ⟨11303427654049546636462477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15071236872066062181949969 11303427654049546636462477)
                    ·
                      refine ⟨4238785370268579988673429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11303427654049546636462477 4238785370268579988673429)
                      ·
                        rfl

theorem cell23_8255005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_8255005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255005 prefixEnd_8255005 := by exact prefixLift 8255005
  have htrace : WordTrace (prefixWord ++ tailWord_8255005) baseStart_8255005 baseEnd_8255005 := by
    simpa [prefixWord, tailWord_8255005, baseEnd_8255005] using wordTrace_append hprefix tailTrace_8255005
  have hstable : (prefixWord ++ tailWord_8255005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255005).length < 2 ^ (prefixWord ++ tailWord_8255005).sum := by decide
  have hdescent : baseEnd_8255005 < baseStart_8255005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255045 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_8255045 : Nat := 118140960795 + 8255045 * 2 ^ 59
def prefixEnd_8255045 : Nat := 4983230072969 + 3 ^ 40 * 8255045 * 2
def baseEnd_8255045 : Nat := 4238805909494759832173245

theorem tailTrace_8255045 : CollatzResearch.WordTrace tailWord_8255045 prefixEnd_8255045 4238805909494759832173245 := by
  unfold tailWord_8255045
  simp only [CollatzResearch.WordTrace]
  refine ⟨301086226378389289287262589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200724150918926192858175059 301086226378389289287262589)
  ·
    refine ⟨112907334891895983482723471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301086226378389289287262589 112907334891895983482723471)
    ·
      refine ⟨169361002337843975224085207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112907334891895983482723471 169361002337843975224085207)
      ·
        refine ⟨254041503506765962836127811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169361002337843975224085207 254041503506765962836127811)
        ·
          refine ⟨381062255260148944254191717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254041503506765962836127811 381062255260148944254191717)
          ·
            refine ⟨71449172861277927047660947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381062255260148944254191717 71449172861277927047660947)
            ·
              refine ⟨107173759291916890571491421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71449172861277927047660947 107173759291916890571491421)
              ·
                refine ⟨40190159734468833964309283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107173759291916890571491421 40190159734468833964309283)
                ·
                  refine ⟨60285239601703250946463925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40190159734468833964309283 60285239601703250946463925)
                  ·
                    refine ⟨5651741212659679776230993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60285239601703250946463925 5651741212659679776230993)
                    ·
                      refine ⟨4238805909494759832173245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651741212659679776230993 4238805909494759832173245)
                      ·
                        rfl

theorem cell23_8255045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_8255045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255045 prefixEnd_8255045 := by exact prefixLift 8255045
  have htrace : WordTrace (prefixWord ++ tailWord_8255045) baseStart_8255045 baseEnd_8255045 := by
    simpa [prefixWord, tailWord_8255045, baseEnd_8255045] using wordTrace_append hprefix tailTrace_8255045
  have hstable : (prefixWord ++ tailWord_8255045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255045).length < 2 ^ (prefixWord ++ tailWord_8255045).sum := by decide
  have hdescent : baseEnd_8255045 < baseStart_8255045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255105 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_8255105 : Nat := 118140960795 + 8255105 * 2 ^ 59
def prefixEnd_8255105 : Nat := 4983230072969 + 3 ^ 40 * 8255105 * 2
def baseEnd_8255105 : Nat := 4238836718334029597422969

theorem tailTrace_8255105 : CollatzResearch.WordTrace tailWord_8255105 prefixEnd_8255105 4238836718334029597422969 := by
  unfold tailWord_8255105
  simp only [CollatzResearch.WordTrace]
  refine ⟨301088414758171919534446769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200725609838781279689631179 301088414758171919534446769)
  ·
    refine ⟨225816311068628939650835077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301088414758171919534446769 225816311068628939650835077)
    ·
      refine ⟨42340558325367926184531577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225816311068628939650835077 42340558325367926184531577)
      ·
        refine ⟨31755418744025944638398683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42340558325367926184531577 31755418744025944638398683)
        ·
          refine ⟨47633128116038916957598025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31755418744025944638398683 47633128116038916957598025)
          ·
            refine ⟨35724846087029187718198519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47633128116038916957598025 35724846087029187718198519)
            ·
              refine ⟨53587269130543781577297779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35724846087029187718198519 53587269130543781577297779)
              ·
                refine ⟨80380903695815672365946669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53587269130543781577297779 80380903695815672365946669)
                ·
                  refine ⟨30142838885930877137230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80380903695815672365946669 30142838885930877137230001)
                  ·
                    refine ⟨22607129164448157852922501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30142838885930877137230001 22607129164448157852922501)
                    ·
                      refine ⟨4238836718334029597422969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22607129164448157852922501 4238836718334029597422969)
                      ·
                        rfl

theorem cell23_8255105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_8255105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255105 prefixEnd_8255105 := by exact prefixLift 8255105
  have htrace : WordTrace (prefixWord ++ tailWord_8255105) baseStart_8255105 baseEnd_8255105 := by
    simpa [prefixWord, tailWord_8255105, baseEnd_8255105] using wordTrace_append hprefix tailTrace_8255105
  have hstable : (prefixWord ++ tailWord_8255105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255105).length < 2 ^ (prefixWord ++ tailWord_8255105).sum := by decide
  have hdescent : baseEnd_8255105 < baseStart_8255105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255132 : List Nat := [2, 2, 3, 2, 3, 2, 1, 8]
def baseStart_8255132 : Nat := 118140960795 + 8255132 * 2 ^ 59
def prefixEnd_8255132 : Nat := 4983230072969 + 3 ^ 40 * 8255132 * 2
def baseEnd_8255132 : Nat := 156994466011544481177235

theorem tailTrace_8255132 : CollatzResearch.WordTrace tailWord_8255132 prefixEnd_8255132 156994466011544481177235 := by
  unfold tailWord_8255132
  simp only [CollatzResearch.WordTrace]
  refine ⟨150544699764537051572839825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200726266352716068763786433 150544699764537051572839825)
  ·
    refine ⟨112908524823402788679629869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150544699764537051572839825 112908524823402788679629869)
    ·
      refine ⟨42340696808776045754861201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112908524823402788679629869 42340696808776045754861201)
      ·
        refine ⟨31755522606582034316145901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42340696808776045754861201 31755522606582034316145901)
        ·
          refine ⟨11908320977468262868554713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31755522606582034316145901 11908320977468262868554713)
          ·
            refine ⟨8931240733101197151416035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11908320977468262868554713 8931240733101197151416035)
            ·
              refine ⟨13396861099651795727124053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931240733101197151416035 13396861099651795727124053)
              ·
                refine ⟨156994466011544481177235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13396861099651795727124053 156994466011544481177235)
                ·
                  rfl

theorem cell23_8255132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 8].length) (baseStart_8255132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255132 prefixEnd_8255132 := by exact prefixLift 8255132
  have htrace : WordTrace (prefixWord ++ tailWord_8255132) baseStart_8255132 baseEnd_8255132 := by
    simpa [prefixWord, tailWord_8255132, baseEnd_8255132] using wordTrace_append hprefix tailTrace_8255132
  have hstable : (prefixWord ++ tailWord_8255132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255132).length < 2 ^ (prefixWord ++ tailWord_8255132).sum := by decide
  have hdescent : baseEnd_8255132 < baseStart_8255132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255152 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2]
def baseStart_8255152 : Nat := 118140960795 + 8255152 * 2 ^ 59
def prefixEnd_8255152 : Nat := 4983230072969 + 3 ^ 40 * 8255152 * 2
def baseEnd_8255152 : Nat := 4238860851924790913535253

theorem tailTrace_8255152 : CollatzResearch.WordTrace tailWord_8255152 prefixEnd_8255152 4238860851924790913535253 := by
  unfold tailWord_8255152
  simp only [CollatzResearch.WordTrace]
  refine ⟨150545064494500823280703855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200726752659334431040938473 150545064494500823280703855)
  ·
    refine ⟨225817596741751234921055783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150545064494500823280703855 225817596741751234921055783)
    ·
      refine ⟨338726395112626852381583675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225817596741751234921055783 338726395112626852381583675)
      ·
        refine ⟨508089592668940278572375513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338726395112626852381583675 508089592668940278572375513)
        ·
          refine ⟨381067194501705208929281635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508089592668940278572375513 381067194501705208929281635)
          ·
            refine ⟨571600791752557813393922453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381067194501705208929281635 571600791752557813393922453)
            ·
              refine ⟨26793787113401147502840115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571600791752557813393922453 26793787113401147502840115)
              ·
                refine ⟨40190680670101721254260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26793787113401147502840115 40190680670101721254260173)
                ·
                  refine ⟨15071505251288145470347565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40190680670101721254260173 15071505251288145470347565)
                  ·
                    refine ⟨5651814469233054551380337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15071505251288145470347565 5651814469233054551380337)
                    ·
                      refine ⟨4238860851924790913535253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651814469233054551380337 4238860851924790913535253)
                      ·
                        rfl

theorem cell23_8255152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2].length) (baseStart_8255152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255152 prefixEnd_8255152 := by exact prefixLift 8255152
  have htrace : WordTrace (prefixWord ++ tailWord_8255152) baseStart_8255152 baseEnd_8255152 := by
    simpa [prefixWord, tailWord_8255152, baseEnd_8255152] using wordTrace_append hprefix tailTrace_8255152
  have hstable : (prefixWord ++ tailWord_8255152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255152).length < 2 ^ (prefixWord ++ tailWord_8255152).sum := by decide
  have hdescent : baseEnd_8255152 < baseStart_8255152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255170 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_8255170 : Nat := 118140960795 + 8255170 * 2 ^ 59
def prefixEnd_8255170 : Nat := 4983230072969 + 3 ^ 40 * 8255170 * 2
def baseEnd_8255170 : Nat := 1412956698192190614370057

theorem tailTrace_8255170 : CollatzResearch.WordTrace tailWord_8255170 prefixEnd_8255170 1412956698192190614370057 := by
  unfold tailWord_8255170
  simp only [CollatzResearch.WordTrace]
  refine ⟨75272696375734108908890741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200727190335290957090375309 75272696375734108908890741)
  ·
    refine ⟨7056815285225072710208507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75272696375734108908890741 7056815285225072710208507)
    ·
      refine ⟨10585222927837609065312761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056815285225072710208507 10585222927837609065312761)
      ·
        refine ⟨7938917195878206798984571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585222927837609065312761 7938917195878206798984571)
        ·
          refine ⟨11908375793817310198476857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938917195878206798984571 11908375793817310198476857)
          ·
            refine ⟨8931281845362982648857643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11908375793817310198476857 8931281845362982648857643)
            ·
              refine ⟨13396922768044473973286465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931281845362982648857643 13396922768044473973286465)
              ·
                refine ⟨10047692076033355479964849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13396922768044473973286465 10047692076033355479964849)
                ·
                  refine ⟨7535769057025016609973637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10047692076033355479964849 7535769057025016609973637)
                  ·
                    refine ⟨1412956698192190614370057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535769057025016609973637 1412956698192190614370057)
                    ·
                      rfl

theorem cell23_8255170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_8255170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255170 prefixEnd_8255170 := by exact prefixLift 8255170
  have htrace : WordTrace (prefixWord ++ tailWord_8255170) baseStart_8255170 baseEnd_8255170 := by
    simpa [prefixWord, tailWord_8255170, baseEnd_8255170] using wordTrace_append hprefix tailTrace_8255170
  have hstable : (prefixWord ++ tailWord_8255170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255170).length < 2 ^ (prefixWord ++ tailWord_8255170).sum := by decide
  have hdescent : baseEnd_8255170 < baseStart_8255170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255205 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 7]
def baseStart_8255205 : Nat := 118140960795 + 8255205 * 2 ^ 59
def prefixEnd_8255205 : Nat := 4983230072969 + 3 ^ 40 * 8255205 * 2
def baseEnd_8255205 : Nat := 470987562933275467352501

theorem tailTrace_8255205 : CollatzResearch.WordTrace tailWord_8255205 prefixEnd_8255205 470987562933275467352501 := by
  unfold tailWord_8255205
  simp only [CollatzResearch.WordTrace]
  refine ⟨301092062057809636613087069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200728041371873091075391379 301092062057809636613087069)
  ·
    refine ⟨112909523271678613729907651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301092062057809636613087069 112909523271678613729907651)
    ·
      refine ⟨169364284907517920594861477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112909523271678613729907651 169364284907517920594861477)
      ·
        refine ⟨31755803420159610111536527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169364284907517920594861477 31755803420159610111536527)
        ·
          refine ⟨47633705130239415167304791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31755803420159610111536527 47633705130239415167304791)
          ·
            refine ⟨71450557695359122750957187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47633705130239415167304791 71450557695359122750957187)
            ·
              refine ⟨107175836543038684126435781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71450557695359122750957187 107175836543038684126435781)
              ·
                refine ⟨20095469351819753273706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107175836543038684126435781 20095469351819753273706709)
                ·
                  refine ⟨470987562933275467352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20095469351819753273706709 470987562933275467352501)
                  ·
                    rfl

theorem cell23_8255205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_8255205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255205 prefixEnd_8255205 := by exact prefixLift 8255205
  have htrace : WordTrace (prefixWord ++ tailWord_8255205) baseStart_8255205 baseEnd_8255205 := by
    simpa [prefixWord, tailWord_8255205, baseEnd_8255205] using wordTrace_append hprefix tailTrace_8255205
  have hstable : (prefixWord ++ tailWord_8255205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255205).length < 2 ^ (prefixWord ++ tailWord_8255205).sum := by decide
  have hdescent : baseEnd_8255205 < baseStart_8255205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255235 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 4, 5]
def baseStart_8255235 : Nat := 118140960795 + 8255235 * 2 ^ 59
def prefixEnd_8255235 : Nat := 4983230072969 + 3 ^ 40 * 8255235 * 2
def baseEnd_8255235 : Nat := 1412967823606371362932457

theorem tailTrace_8255235 : CollatzResearch.WordTrace tailWord_8255235 prefixEnd_8255235 1412967823606371362932457 := by
  unfold tailWord_8255235
  simp only [CollatzResearch.WordTrace]
  refine ⟨301093156247700951736679159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200728770831800634491119439 301093156247700951736679159)
  ·
    refine ⟨451639734371551427605018739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301093156247700951736679159 451639734371551427605018739)
    ·
      refine ⟨677459601557327141407528109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451639734371551427605018739 677459601557327141407528109)
      ·
        refine ⟨254047350583997678027823041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677459601557327141407528109 254047350583997678027823041)
        ·
          refine ⟨190535512937998258520867281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254047350583997678027823041 190535512937998258520867281)
          ·
            refine ⟨142901634703498693890650461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190535512937998258520867281 142901634703498693890650461)
            ·
              refine ⟨53588113013812010208993923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142901634703498693890650461 53588113013812010208993923)
              ·
                refine ⟨80382169520718015313490885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53588113013812010208993923 80382169520718015313490885)
                ·
                  refine ⟨15071656785134627871279541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80382169520718015313490885 15071656785134627871279541)
                  ·
                    refine ⟨1412967823606371362932457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15071656785134627871279541 1412967823606371362932457)
                    ·
                      rfl

theorem cell23_8255235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].length) (baseStart_8255235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255235 prefixEnd_8255235 := by exact prefixLift 8255235
  have htrace : WordTrace (prefixWord ++ tailWord_8255235) baseStart_8255235 baseEnd_8255235 := by
    simpa [prefixWord, tailWord_8255235, baseEnd_8255235] using wordTrace_append hprefix tailTrace_8255235
  have hstable : (prefixWord ++ tailWord_8255235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255235).length < 2 ^ (prefixWord ++ tailWord_8255235).sum := by decide
  have hdescent : baseEnd_8255235 < baseStart_8255235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255239 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 7]
def baseStart_8255239 : Nat := 118140960795 + 8255239 * 2 ^ 59
def prefixEnd_8255239 : Nat := 4983230072969 + 3 ^ 40 * 8255239 * 2
def baseEnd_8255239 : Nat := 470989502749081341460817

theorem tailTrace_8255239 : CollatzResearch.WordTrace tailWord_8255239 prefixEnd_8255239 470989502749081341460817 := by
  unfold tailWord_8255239
  simp only [CollatzResearch.WordTrace]
  refine ⟨301093302139686460419824771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200728868093124306946549847 301093302139686460419824771)
  ·
    refine ⟨451639953209529690629737157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301093302139686460419824771 451639953209529690629737157)
    ·
      refine ⟨84682491226786816993075717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451639953209529690629737157 84682491226786816993075717)
      ·
        refine ⟨15877967105022528186201697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84682491226786816993075717 15877967105022528186201697)
        ·
          refine ⟨11908475328766896139651273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15877967105022528186201697 11908475328766896139651273)
          ·
            refine ⟨8931356496575172104738455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11908475328766896139651273 8931356496575172104738455)
            ·
              refine ⟨13397034744862758157107683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931356496575172104738455 13397034744862758157107683)
              ·
                refine ⟨20095552117294137235661525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397034744862758157107683 20095552117294137235661525)
                ·
                  refine ⟨470989502749081341460817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20095552117294137235661525 470989502749081341460817)
                  ·
                    rfl

theorem cell23_8255239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 7].length) (baseStart_8255239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255239 prefixEnd_8255239 := by exact prefixLift 8255239
  have htrace : WordTrace (prefixWord ++ tailWord_8255239) baseStart_8255239 baseEnd_8255239 := by
    simpa [prefixWord, tailWord_8255239, baseEnd_8255239] using wordTrace_append hprefix tailTrace_8255239
  have hstable : (prefixWord ++ tailWord_8255239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255239).length < 2 ^ (prefixWord ++ tailWord_8255239).sum := by decide
  have hdescent : baseEnd_8255239 < baseStart_8255239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255250 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_8255250 : Nat := 118140960795 + 8255250 * 2 ^ 59
def prefixEnd_8255250 : Nat := 4983230072969 + 3 ^ 40 * 8255250 * 2
def baseEnd_8255250 : Nat := 4238911173028931530109803

theorem tailTrace_8255250 : CollatzResearch.WordTrace tailWord_8255250 prefixEnd_8255250 4238911173028931530109803 := by
  unfold tailWord_8255250
  simp only [CollatzResearch.WordTrace]
  refine ⟨75273425835661652324618801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200729135561764406198983469 75273425835661652324618801)
  ·
    refine ⟨56455069376746239243464101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75273425835661652324618801 56455069376746239243464101)
    ·
      refine ⟨10585325508139919858149519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56455069376746239243464101 10585325508139919858149519)
      ·
        refine ⟨15877988262209879787224279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10585325508139919858149519 15877988262209879787224279)
        ·
          refine ⟨23816982393314819680836419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15877988262209879787224279 23816982393314819680836419)
          ·
            refine ⟨35725473589972229521254629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23816982393314819680836419 35725473589972229521254629)
            ·
              refine ⟨6698526298119793035235243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35725473589972229521254629 6698526298119793035235243)
              ·
                refine ⟨10047789447179689552852865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698526298119793035235243 10047789447179689552852865)
                ·
                  refine ⟨7535842085384767164639649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10047789447179689552852865 7535842085384767164639649)
                  ·
                    refine ⟨5651881564038575373479737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7535842085384767164639649 5651881564038575373479737)
                    ·
                      refine ⟨4238911173028931530109803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651881564038575373479737 4238911173028931530109803)
                      ·
                        rfl

theorem cell23_8255250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_8255250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255250 prefixEnd_8255250 := by exact prefixLift 8255250
  have htrace : WordTrace (prefixWord ++ tailWord_8255250) baseStart_8255250 baseEnd_8255250 := by
    simpa [prefixWord, tailWord_8255250, baseEnd_8255250] using wordTrace_append hprefix tailTrace_8255250
  have hstable : (prefixWord ++ tailWord_8255250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255250).length < 2 ^ (prefixWord ++ tailWord_8255250).sum := by decide
  have hdescent : baseEnd_8255250 < baseStart_8255250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255389 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_8255389 : Nat := 118140960795 + 8255389 * 2 ^ 59
def prefixEnd_8255389 : Nat := 4983230072969 + 3 ^ 40 * 8255389 * 2
def baseEnd_8255389 : Nat := 1412994182279968828757221

theorem tailTrace_8255389 : CollatzResearch.WordTrace tailWord_8255389 prefixEnd_8255389 1412994182279968828757221 := by
  unfold tailWord_8255389
  simp only [CollatzResearch.WordTrace]
  refine ⟨301098773089143036037785221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200732515392762024025190147 301098773089143036037785221)
  ·
    refine ⟨56456019954214319257084729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301098773089143036037785221 56456019954214319257084729)
    ·
      refine ⟨42342014965660739442813547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56456019954214319257084729 42342014965660739442813547)
      ·
        refine ⟨63513022448491109164220321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42342014965660739442813547 63513022448491109164220321)
        ·
          refine ⟨47634766836368331873165241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63513022448491109164220321 47634766836368331873165241)
          ·
            refine ⟨35726075127276248904873931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47634766836368331873165241 35726075127276248904873931)
            ·
              refine ⟨53589112690914373357310897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35726075127276248904873931 53589112690914373357310897)
              ·
                refine ⟨40191834518185780017983173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53589112690914373357310897 40191834518185780017983173)
                ·
                  refine ⟨7535968972159833753371845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40191834518185780017983173 7535968972159833753371845)
                  ·
                    refine ⟨1412994182279968828757221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535968972159833753371845 1412994182279968828757221)
                    ·
                      rfl

theorem cell23_8255389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_8255389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255389 prefixEnd_8255389 := by exact prefixLift 8255389
  have htrace : WordTrace (prefixWord ++ tailWord_8255389) baseStart_8255389 baseEnd_8255389 := by
    simpa [prefixWord, tailWord_8255389, baseEnd_8255389] using wordTrace_append hprefix tailTrace_8255389
  have hstable : (prefixWord ++ tailWord_8255389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255389).length < 2 ^ (prefixWord ++ tailWord_8255389).sum := by decide
  have hdescent : baseEnd_8255389 < baseStart_8255389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255392 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_8255392 : Nat := 118140960795 + 8255392 * 2 ^ 59
def prefixEnd_8255392 : Nat := 4983230072969 + 3 ^ 40 * 8255392 * 2
def baseEnd_8255392 : Nat := 4238984087281869974534149

theorem tailTrace_8255392 : CollatzResearch.WordTrace tailWord_8255392 prefixEnd_8255392 4238984087281869974534149 := by
  unfold tailWord_8255392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150549441254066083775072215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200732588338754778366762953 150549441254066083775072215)
  ·
    refine ⟨225824161881099125662608323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150549441254066083775072215 225824161881099125662608323)
    ·
      refine ⟨338736242821648688493912485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225824161881099125662608323 338736242821648688493912485)
      ·
        refine ⟨63513045529059129092608591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338736242821648688493912485 63513045529059129092608591)
        ·
          refine ⟨95269568293588693638912887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63513045529059129092608591 95269568293588693638912887)
          ·
            refine ⟨142904352440383040458369331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95269568293588693638912887 142904352440383040458369331)
            ·
              refine ⟨214356528660574560687553997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142904352440383040458369331 214356528660574560687553997)
              ·
                refine ⟨80383698247715460257832749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214356528660574560687553997 80383698247715460257832749)
                ·
                  refine ⟨30143886842893297596687281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80383698247715460257832749 30143886842893297596687281)
                  ·
                    refine ⟨22607915132169973197515461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30143886842893297596687281 22607915132169973197515461)
                    ·
                      refine ⟨4238984087281869974534149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22607915132169973197515461 4238984087281869974534149)
                      ·
                        rfl

theorem cell23_8255392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_8255392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255392 prefixEnd_8255392 := by exact prefixLift 8255392
  have htrace : WordTrace (prefixWord ++ tailWord_8255392) baseStart_8255392 baseEnd_8255392 := by
    simpa [prefixWord, tailWord_8255392, baseEnd_8255392] using wordTrace_append hprefix tailTrace_8255392
  have hstable : (prefixWord ++ tailWord_8255392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255392).length < 2 ^ (prefixWord ++ tailWord_8255392).sum := by decide
  have hdescent : baseEnd_8255392 < baseStart_8255392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255399 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_8255399 : Nat := 118140960795 + 8255399 * 2 ^ 59
def prefixEnd_8255399 : Nat := 4983230072969 + 3 ^ 40 * 8255399 * 2
def baseEnd_8255399 : Nat := 4238987681646451447146617

theorem tailTrace_8255399 : CollatzResearch.WordTrace tailWord_8255399 prefixEnd_8255399 4238987681646451447146617 := by
  unfold tailWord_8255399
  simp only [CollatzResearch.WordTrace]
  refine ⟨301099137819106807745649251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200732758546071205163766167 301099137819106807745649251)
  ·
    refine ⟨451648706728660211618473877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301099137819106807745649251 451648706728660211618473877)
    ·
      refine ⟨21171033127905947419615963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 451648706728660211618473877 21171033127905947419615963)
      ·
        refine ⟨31756549691858921129423945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21171033127905947419615963 31756549691858921129423945)
        ·
          refine ⟨23817412268894190847067959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31756549691858921129423945 23817412268894190847067959)
          ·
            refine ⟨35726118403341286270601939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23817412268894190847067959 35726118403341286270601939)
            ·
              refine ⟨53589177605011929405902909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35726118403341286270601939 53589177605011929405902909)
              ·
                refine ⟨20095941601879473527213591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53589177605011929405902909 20095941601879473527213591)
                ·
                  refine ⟨30143912402819210290820387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20095941601879473527213591 30143912402819210290820387)
                  ·
                    refine ⟨45215868604228815436230581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30143912402819210290820387 45215868604228815436230581)
                    ·
                      refine ⟨4238987681646451447146617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45215868604228815436230581 4238987681646451447146617)
                      ·
                        rfl

theorem cell23_8255399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_8255399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255399 prefixEnd_8255399 := by exact prefixLift 8255399
  have htrace : WordTrace (prefixWord ++ tailWord_8255399) baseStart_8255399 baseEnd_8255399 := by
    simpa [prefixWord, tailWord_8255399, baseEnd_8255399] using wordTrace_append hprefix tailTrace_8255399
  have hstable : (prefixWord ++ tailWord_8255399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255399).length < 2 ^ (prefixWord ++ tailWord_8255399).sum := by decide
  have hdescent : baseEnd_8255399 < baseStart_8255399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255400 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8255400 : Nat := 118140960795 + 8255400 * 2 ^ 59
def prefixEnd_8255400 : Nat := 4983230072969 + 3 ^ 40 * 8255400 * 2
def baseEnd_8255400 : Nat := 4238988195127105943234113

theorem tailTrace_8255400 : CollatzResearch.WordTrace tailWord_8255400 prefixEnd_8255400 4238988195127105943234113 := by
  unfold tailWord_8255400
  simp only [CollatzResearch.WordTrace]
  refine ⟨150549587146051592458217827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200732782861402123277623769 150549587146051592458217827)
  ·
    refine ⟨225824380719077388687326741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150549587146051592458217827 225824380719077388687326741)
    ·
      refine ⟨10585517846206752594718441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225824380719077388687326741 10585517846206752594718441)
      ·
        refine ⟨7939138384655064446038831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585517846206752594718441 7939138384655064446038831)
        ·
          refine ⟨11908707576982596669058247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939138384655064446038831 11908707576982596669058247)
          ·
            refine ⟨17863061365473895003587371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908707576982596669058247 17863061365473895003587371)
            ·
              refine ⟨26794592048210842505381057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863061365473895003587371 26794592048210842505381057)
              ·
                refine ⟨20095944036158131879035793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26794592048210842505381057 20095944036158131879035793)
                ·
                  refine ⟨15071958027118598909276845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20095944036158131879035793 15071958027118598909276845)
                  ·
                    refine ⟨5651984260169474590978817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15071958027118598909276845 5651984260169474590978817)
                    ·
                      refine ⟨4238988195127105943234113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651984260169474590978817 4238988195127105943234113)
                      ·
                        rfl

theorem cell23_8255400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8255400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255400 prefixEnd_8255400 := by exact prefixLift 8255400
  have htrace : WordTrace (prefixWord ++ tailWord_8255400) baseStart_8255400 baseEnd_8255400 := by
    simpa [prefixWord, tailWord_8255400, baseEnd_8255400] using wordTrace_append hprefix tailTrace_8255400
  have hstable : (prefixWord ++ tailWord_8255400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255400).length < 2 ^ (prefixWord ++ tailWord_8255400).sum := by decide
  have hdescent : baseEnd_8255400 < baseStart_8255400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255413 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_8255413 : Nat := 118140960795 + 8255413 * 2 ^ 59
def prefixEnd_8255413 : Nat := 4983230072969 + 3 ^ 40 * 8255413 * 2
def baseEnd_8255413 : Nat := 4238994870375614392371553

theorem tailTrace_8255413 : CollatzResearch.WordTrace tailWord_8255413 prefixEnd_8255413 4238994870375614392371553 := by
  unfold tailWord_8255413
  simp only [CollatzResearch.WordTrace]
  refine ⟨301099648441056088136658893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200733098960704058757772595 301099648441056088136658893)
  ·
    refine ⟨112912368165396033051247085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301099648441056088136658893 112912368165396033051247085)
    ·
      refine ⟨42342138062023512394217657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112912368165396033051247085 42342138062023512394217657)
      ·
        refine ⟨31756603546517634295663243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42342138062023512394217657 31756603546517634295663243)
        ·
          refine ⟨47634905319776451443494865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31756603546517634295663243 47634905319776451443494865)
          ·
            refine ⟨35726178989832338582621149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47634905319776451443494865 35726178989832338582621149)
            ·
              refine ⟨13397317121187126968482931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35726178989832338582621149 13397317121187126968482931)
              ·
                refine ⟨20095975681780690452724397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397317121187126968482931 20095975681780690452724397)
                ·
                  refine ⟨7535990880667758919771649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20095975681780690452724397 7535990880667758919771649)
                  ·
                    refine ⟨5651993160500819189828737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7535990880667758919771649 5651993160500819189828737)
                    ·
                      refine ⟨4238994870375614392371553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5651993160500819189828737 4238994870375614392371553)
                      ·
                        rfl

theorem cell23_8255413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_8255413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255413 prefixEnd_8255413 := by exact prefixLift 8255413
  have htrace : WordTrace (prefixWord ++ tailWord_8255413) baseStart_8255413 baseEnd_8255413 := by
    simpa [prefixWord, tailWord_8255413, baseEnd_8255413] using wordTrace_append hprefix tailTrace_8255413
  have hstable : (prefixWord ++ tailWord_8255413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255413).length < 2 ^ (prefixWord ++ tailWord_8255413).sum := by decide
  have hdescent : baseEnd_8255413 < baseStart_8255413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255429 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_8255429 : Nat := 118140960795 + 8255429 * 2 ^ 59
def prefixEnd_8255429 : Nat := 4983230072969 + 3 ^ 40 * 8255429 * 2
def baseEnd_8255429 : Nat := 4239003086066086329771479

theorem tailTrace_8255429 : CollatzResearch.WordTrace tailWord_8255429 prefixEnd_8255429 4239003086066086329771479 := by
  unfold tailWord_8255429
  simp only [CollatzResearch.WordTrace]
  refine ⟨301100232008998122869241341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200733488005998748579494227 301100232008998122869241341)
  ·
    refine ⟨112912587003374296075965503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301100232008998122869241341 112912587003374296075965503)
    ·
      refine ⟨169368880505061444113948255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112912587003374296075965503 169368880505061444113948255)
      ·
        refine ⟨254053320757592166170922383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169368880505061444113948255 254053320757592166170922383)
        ·
          refine ⟨381079981136388249256383575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254053320757592166170922383 381079981136388249256383575)
          ·
            refine ⟨571619971704582373884575363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381079981136388249256383575 571619971704582373884575363)
            ·
              refine ⟨857429957556873560826863045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571619971704582373884575363 857429957556873560826863045)
              ·
                refine ⟨160768117041913792655036821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 857429957556873560826863045 160768117041913792655036821)
                ·
                  refine ⟨7536005486339709030704851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160768117041913792655036821 7536005486339709030704851)
                  ·
                    refine ⟨11304008229509563546057277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7536005486339709030704851 11304008229509563546057277)
                    ·
                      refine ⟨4239003086066086329771479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304008229509563546057277 4239003086066086329771479)
                      ·
                        rfl

theorem cell23_8255429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_8255429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255429 prefixEnd_8255429 := by exact prefixLift 8255429
  have htrace : WordTrace (prefixWord ++ tailWord_8255429) baseStart_8255429 baseEnd_8255429 := by
    simpa [prefixWord, tailWord_8255429, baseEnd_8255429] using wordTrace_append hprefix tailTrace_8255429
  have hstable : (prefixWord ++ tailWord_8255429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255429).length < 2 ^ (prefixWord ++ tailWord_8255429).sum := by decide
  have hdescent : baseEnd_8255429 < baseStart_8255429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255456 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2]
def baseStart_8255456 : Nat := 118140960795 + 8255456 * 2 ^ 59
def prefixEnd_8255456 : Nat := 4983230072969 + 3 ^ 40 * 8255456 * 2
def baseEnd_8255456 : Nat := 4239016950043757724133855

theorem tailTrace_8255456 : CollatzResearch.WordTrace tailWord_8255456 prefixEnd_8255456 4239016950043757724133855 := by
  unfold tailWord_8255456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150550608389950153240237111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200734144519933537653649481 150550608389950153240237111)
  ·
    refine ⟨225825912584925229860355667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150550608389950153240237111 225825912584925229860355667)
    ·
      refine ⟨338738868877387844790533501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225825912584925229860355667 338738868877387844790533501)
      ·
        refine ⟨127027075829020441796450063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338738868877387844790533501 127027075829020441796450063)
        ·
          refine ⟨190540613743530662694675095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127027075829020441796450063 190540613743530662694675095)
          ·
            refine ⟨285810920615295994042012643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190540613743530662694675095 285810920615295994042012643)
            ·
              refine ⟨428716380922943991063018965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285810920615295994042012643 428716380922943991063018965)
              ·
                refine ⟨10048040177881499790539507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 428716380922943991063018965 10048040177881499790539507)
                ·
                  refine ⟨15072060266822249685809261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048040177881499790539507 15072060266822249685809261)
                  ·
                    refine ⟨5652022600058343632178473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15072060266822249685809261 5652022600058343632178473)
                    ·
                      refine ⟨4239016950043757724133855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652022600058343632178473 4239016950043757724133855)
                      ·
                        rfl

theorem cell23_8255456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_8255456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255456 prefixEnd_8255456 := by exact prefixLift 8255456
  have htrace : WordTrace (prefixWord ++ tailWord_8255456) baseStart_8255456 baseEnd_8255456 := by
    simpa [prefixWord, tailWord_8255456, baseEnd_8255456] using wordTrace_append hprefix tailTrace_8255456
  have hstable : (prefixWord ++ tailWord_8255456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255456).length < 2 ^ (prefixWord ++ tailWord_8255456).sum := by decide
  have hdescent : baseEnd_8255456 < baseStart_8255456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255472 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_8255472 : Nat := 118140960795 + 8255472 * 2 ^ 59
def prefixEnd_8255472 : Nat := 4983230072969 + 3 ^ 40 * 8255472 * 2
def baseEnd_8255472 : Nat := 4239025165734229661533781

theorem tailTrace_8255472 : CollatzResearch.WordTrace tailWord_8255472 prefixEnd_8255472 4239025165734229661533781 := by
  unfold tailWord_8255472
  simp only [CollatzResearch.WordTrace]
  refine ⟨150550900173921170606528335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200734533565228227475371113 150550900173921170606528335)
  ·
    refine ⟨225826350260881755909792503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150550900173921170606528335 225826350260881755909792503)
    ·
      refine ⟨338739525391322633864688755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225826350260881755909792503 338739525391322633864688755)
      ·
        refine ⟨508109288086983950797033133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338739525391322633864688755 508109288086983950797033133)
        ·
          refine ⟨190540983032618981548887425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508109288086983950797033133 190540983032618981548887425)
          ·
            refine ⟨142905737274464236161665569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190540983032618981548887425 142905737274464236161665569)
            ·
              refine ⟨107179302955848177121249177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142905737274464236161665569 107179302955848177121249177)
              ·
                refine ⟨80384477216886132840936883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107179302955848177121249177 80384477216886132840936883)
                ·
                  refine ⟨120576715825329199261405325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80384477216886132840936883 120576715825329199261405325)
                  ·
                    refine ⟨45216268434498449723026997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120576715825329199261405325 45216268434498449723026997)
                    ·
                      refine ⟨4239025165734229661533781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45216268434498449723026997 4239025165734229661533781)
                      ·
                        rfl

theorem cell23_8255472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_8255472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255472 prefixEnd_8255472 := by exact prefixLift 8255472
  have htrace : WordTrace (prefixWord ++ tailWord_8255472) baseStart_8255472 baseEnd_8255472 := by
    simpa [prefixWord, tailWord_8255472, baseEnd_8255472] using wordTrace_append hprefix tailTrace_8255472
  have hstable : (prefixWord ++ tailWord_8255472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255472).length < 2 ^ (prefixWord ++ tailWord_8255472).sum := by decide
  have hdescent : baseEnd_8255472 < baseStart_8255472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255489 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_8255489 : Nat := 118140960795 + 8255489 * 2 ^ 59
def prefixEnd_8255489 : Nat := 4983230072969 + 3 ^ 40 * 8255489 * 2
def baseEnd_8255489 : Nat := 4239033894905356095021203

theorem tailTrace_8255489 : CollatzResearch.WordTrace tailWord_8255489 prefixEnd_8255489 4239033894905356095021203 := by
  unfold tailWord_8255489
  simp only [CollatzResearch.WordTrace]
  refine ⟨301102420388780753116425521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200734946925853835410950347 301102420388780753116425521)
  ·
    refine ⟨225826815291585564837319141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301102420388780753116425521 225826815291585564837319141)
    ·
      refine ⟨42342527867172293406997339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225826815291585564837319141 42342527867172293406997339)
      ·
        refine ⟨63513791800758440110496009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42342527867172293406997339 63513791800758440110496009)
        ·
          refine ⟨47635343850568830082872007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63513791800758440110496009 47635343850568830082872007)
          ·
            refine ⟨71453015775853245124308011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47635343850568830082872007 71453015775853245124308011)
            ·
              refine ⟨107179523663779867686462017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71453015775853245124308011 107179523663779867686462017)
              ·
                refine ⟨80384642747834900764846513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107179523663779867686462017 80384642747834900764846513)
                ·
                  refine ⟨60288482060876175573634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80384642747834900764846513 60288482060876175573634885)
                  ·
                    refine ⟨11304090386414282920056541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60288482060876175573634885 11304090386414282920056541)
                    ·
                      refine ⟨4239033894905356095021203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304090386414282920056541 4239033894905356095021203)
                      ·
                        rfl

theorem cell23_8255489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_8255489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255489 prefixEnd_8255489 := by exact prefixLift 8255489
  have htrace : WordTrace (prefixWord ++ tailWord_8255489) baseStart_8255489 baseEnd_8255489 := by
    simpa [prefixWord, tailWord_8255489, baseEnd_8255489] using wordTrace_append hprefix tailTrace_8255489
  have hstable : (prefixWord ++ tailWord_8255489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255489).length < 2 ^ (prefixWord ++ tailWord_8255489).sum := by decide
  have hdescent : baseEnd_8255489 < baseStart_8255489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255501 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8255501 : Nat := 118140960795 + 8255501 * 2 ^ 59
def prefixEnd_8255501 : Nat := 4983230072969 + 3 ^ 40 * 8255501 * 2
def baseEnd_8255501 : Nat := 4239040056673210048071149

theorem tailTrace_8255501 : CollatzResearch.WordTrace tailWord_8255501 prefixEnd_8255501 4239040056673210048071149 := by
  unfold tailWord_8255501
  simp only [CollatzResearch.WordTrace]
  refine ⟨301102858064737279165862357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200735238709824852777241571 301102858064737279165862357)
  ·
    refine ⟨7057098235892279980449899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 301102858064737279165862357 7057098235892279980449899)
    ·
      refine ⟨10585647353838419970674849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057098235892279980449899 10585647353838419970674849)
      ·
        refine ⟨7939235515378814978006137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585647353838419970674849 7939235515378814978006137)
        ·
          refine ⟨5954426636534111233504603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939235515378814978006137 5954426636534111233504603)
          ·
            refine ⟨8931639954801166850256905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954426636534111233504603 8931639954801166850256905)
            ·
              refine ⟨6698729966100875137692679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8931639954801166850256905 6698729966100875137692679)
              ·
                refine ⟨10048094949151312706539019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698729966100875137692679 10048094949151312706539019)
                ·
                  refine ⟨15072142423726969059808529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048094949151312706539019 15072142423726969059808529)
                  ·
                    refine ⟨11304106817795226794856397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15072142423726969059808529 11304106817795226794856397)
                    ·
                      refine ⟨4239040056673210048071149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304106817795226794856397 4239040056673210048071149)
                      ·
                        rfl

theorem cell23_8255501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8255501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255501 prefixEnd_8255501 := by exact prefixLift 8255501
  have htrace : WordTrace (prefixWord ++ tailWord_8255501) baseStart_8255501 baseEnd_8255501 := by
    simpa [prefixWord, tailWord_8255501, baseEnd_8255501] using wordTrace_append hprefix tailTrace_8255501
  have hstable : (prefixWord ++ tailWord_8255501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255501).length < 2 ^ (prefixWord ++ tailWord_8255501).sum := by decide
  have hdescent : baseEnd_8255501 < baseStart_8255501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255519 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_8255519 : Nat := 118140960795 + 8255519 * 2 ^ 59
def prefixEnd_8255519 : Nat := 4983230072969 + 3 ^ 40 * 8255519 * 2
def baseEnd_8255519 : Nat := 4239049299324990977646065

theorem tailTrace_8255519 : CollatzResearch.WordTrace tailWord_8255519 prefixEnd_8255519 4239049299324990977646065 := by
  unfold tailWord_8255519
  simp only [CollatzResearch.WordTrace]
  refine ⟨301103514578672068240017611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200735676385781378826678407 301103514578672068240017611)
  ·
    refine ⟨451655271868008102360026417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301103514578672068240017611 451655271868008102360026417)
    ·
      refine ⟨338741453901006076770019813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451655271868008102360026417 338741453901006076770019813)
      ·
        refine ⟨63514022606438639394378715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338741453901006076770019813 63514022606438639394378715)
        ·
          refine ⟨95271033909657959091568073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63514022606438639394378715 95271033909657959091568073)
          ·
            refine ⟨71453275432243469318676055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95271033909657959091568073 71453275432243469318676055)
            ·
              refine ⟨107179913148365203978014083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71453275432243469318676055 107179913148365203978014083)
              ·
                refine ⟨160769869722547805967021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107179913148365203978014083 160769869722547805967021125)
                ·
                  refine ⟨30144350572977713618816461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160769869722547805967021125 30144350572977713618816461)
                  ·
                    refine ⟨11304131464866642607056173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30144350572977713618816461 11304131464866642607056173)
                    ·
                      refine ⟨4239049299324990977646065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304131464866642607056173 4239049299324990977646065)
                      ·
                        rfl

theorem cell23_8255519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_8255519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255519 prefixEnd_8255519 := by exact prefixLift 8255519
  have htrace : WordTrace (prefixWord ++ tailWord_8255519) baseStart_8255519 baseEnd_8255519 := by
    simpa [prefixWord, tailWord_8255519, baseEnd_8255519] using wordTrace_append hprefix tailTrace_8255519
  have hstable : (prefixWord ++ tailWord_8255519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255519).length < 2 ^ (prefixWord ++ tailWord_8255519).sum := by decide
  have hdescent : baseEnd_8255519 < baseStart_8255519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255559 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_8255559 : Nat := 118140960795 + 8255559 * 2 ^ 59
def prefixEnd_8255559 : Nat := 4983230072969 + 3 ^ 40 * 8255559 * 2
def baseEnd_8255559 : Nat := 4239069838551170821145881

theorem tailTrace_8255559 : CollatzResearch.WordTrace tailWord_8255559 prefixEnd_8255559 4239069838551170821145881 := by
  unfold tailWord_8255559
  simp only [CollatzResearch.WordTrace]
  refine ⟨301104973498527155071473731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200736648999018103380982487 301104973498527155071473731)
  ·
    refine ⟨451657460247790732607210597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301104973498527155071473731 451657460247790732607210597)
    ·
      refine ⟨84685773796460762363851987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451657460247790732607210597 84685773796460762363851987)
      ·
        refine ⟨127028660694691143545777981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84685773796460762363851987 127028660694691143545777981)
        ·
          refine ⟨47635747760509178829666743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127028660694691143545777981 47635747760509178829666743)
          ·
            refine ⟨71453621640763768244500115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47635747760509178829666743 71453621640763768244500115)
            ·
              refine ⟨107180432461145652366750173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71453621640763768244500115 107180432461145652366750173)
              ·
                refine ⟨40192662172929619637531315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107180432461145652366750173 40192662172929619637531315)
                ·
                  refine ⟨60288993259394429456296973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40192662172929619637531315 60288993259394429456296973)
                  ·
                    refine ⟨22608372472272911046111365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60288993259394429456296973 22608372472272911046111365)
                    ·
                      refine ⟨4239069838551170821145881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22608372472272911046111365 4239069838551170821145881)
                      ·
                        rfl

theorem cell23_8255559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_8255559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255559 prefixEnd_8255559 := by exact prefixLift 8255559
  have htrace : WordTrace (prefixWord ++ tailWord_8255559) baseStart_8255559 baseEnd_8255559 := by
    simpa [prefixWord, tailWord_8255559, baseEnd_8255559] using wordTrace_append hprefix tailTrace_8255559
  have hstable : (prefixWord ++ tailWord_8255559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255559).length < 2 ^ (prefixWord ++ tailWord_8255559).sum := by decide
  have hdescent : baseEnd_8255559 < baseStart_8255559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255576 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_8255576 : Nat := 118140960795 + 8255576 * 2 ^ 59
def prefixEnd_8255576 : Nat := 4983230072969 + 3 ^ 40 * 8255576 * 2
def baseEnd_8255576 : Nat := 4239078567722297254633303

theorem tailTrace_8255576 : CollatzResearch.WordTrace tailWord_8255576 prefixEnd_8255576 4239078567722297254633303 := by
  unfold tailWord_8255576
  simp only [CollatzResearch.WordTrace]
  refine ⟨150552796769732783487421291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200737062359643711316561721 150552796769732783487421291)
  ·
    refine ⟨225829195154599175231131937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150552796769732783487421291 225829195154599175231131937)
    ·
      refine ⟨169371896365949381423348953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225829195154599175231131937 169371896365949381423348953)
      ·
        refine ⟨127028922274462036067511715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169371896365949381423348953 127028922274462036067511715)
        ·
          refine ⟨190543383411693054101267573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127028922274462036067511715 190543383411693054101267573)
          ·
            refine ⟨17863442194846223821993835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190543383411693054101267573 17863442194846223821993835)
            ·
              refine ⟨26795163292269335732990753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863442194846223821993835 26795163292269335732990753)
              ·
                refine ⟨20096372469202001799743065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26795163292269335732990753 20096372469202001799743065)
                ·
                  refine ⟨15072279351901501349807299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20096372469202001799743065 15072279351901501349807299)
                  ·
                    refine ⟨22608419027852252024710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15072279351901501349807299 22608419027852252024710949)
                    ·
                      refine ⟨4239078567722297254633303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22608419027852252024710949 4239078567722297254633303)
                      ·
                        rfl

theorem cell23_8255576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_8255576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255576 prefixEnd_8255576 := by exact prefixLift 8255576
  have htrace : WordTrace (prefixWord ++ tailWord_8255576) baseStart_8255576 baseEnd_8255576 := by
    simpa [prefixWord, tailWord_8255576, baseEnd_8255576] using wordTrace_append hprefix tailTrace_8255576
  have hstable : (prefixWord ++ tailWord_8255576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255576).length < 2 ^ (prefixWord ++ tailWord_8255576).sum := by decide
  have hdescent : baseEnd_8255576 < baseStart_8255576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255613 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_8255613 : Nat := 118140960795 + 8255613 * 2 ^ 59
def prefixEnd_8255613 : Nat := 4983230072969 + 3 ^ 40 * 8255613 * 2
def baseEnd_8255613 : Nat := 4239097566506513609870633

theorem tailTrace_8255613 : CollatzResearch.WordTrace tailWord_8255613 prefixEnd_8255613 4239097566506513609870633 := by
  unfold tailWord_8255613
  simp only [CollatzResearch.WordTrace]
  refine ⟨301106943040331522293939493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200737962026887681529292995 301106943040331522293939493)
  ·
    refine ⟨56457551820062160430113655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301106943040331522293939493 56457551820062160430113655)
    ·
      refine ⟨84686327730093240645170483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56457551820062160430113655 84686327730093240645170483)
      ·
        refine ⟨127029491595139860967755725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84686327730093240645170483 127029491595139860967755725)
        ·
          refine ⟨47636059348177447862908397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127029491595139860967755725 47636059348177447862908397)
          ·
            refine ⟨17863522255566542948590649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47636059348177447862908397 17863522255566542948590649)
            ·
              refine ⟨13397641691674907211442987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863522255566542948590649 13397641691674907211442987)
              ·
                refine ⟨20096462537512360817164481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397641691674907211442987 20096462537512360817164481)
                ·
                  refine ⟨15072346903134270612873361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20096462537512360817164481 15072346903134270612873361)
                  ·
                    refine ⟨11304260177350702959655021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15072346903134270612873361 11304260177350702959655021)
                    ·
                      refine ⟨4239097566506513609870633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304260177350702959655021 4239097566506513609870633)
                      ·
                        rfl

theorem cell23_8255613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_8255613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255613 prefixEnd_8255613 := by exact prefixLift 8255613
  have htrace : WordTrace (prefixWord ++ tailWord_8255613) baseStart_8255613 baseEnd_8255613 := by
    simpa [prefixWord, tailWord_8255613, baseEnd_8255613] using wordTrace_append hprefix tailTrace_8255613
  have hstable : (prefixWord ++ tailWord_8255613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255613).length < 2 ^ (prefixWord ++ tailWord_8255613).sum := by decide
  have hdescent : baseEnd_8255613 < baseStart_8255613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255666 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_8255666 : Nat := 118140960795 + 8255666 * 2 ^ 59
def prefixEnd_8255666 : Nat := 4983230072969 + 3 ^ 40 * 8255666 * 2
def baseEnd_8255666 : Nat := 4239124780981201902507889

theorem tailTrace_8255666 : CollatzResearch.WordTrace tailWord_8255666 prefixEnd_8255666 4239124780981201902507889 := by
  unfold tailWord_8255666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75277219027284878086404713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200739250739426341563745901 75277219027284878086404713)
  ·
    refine ⟨56457914270463658564803535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75277219027284878086404713 56457914270463658564803535)
    ·
      refine ⟨84686871405695487847205303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56457914270463658564803535 84686871405695487847205303)
      ·
        refine ⟨127030307108543231770807955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84686871405695487847205303 127030307108543231770807955)
        ·
          refine ⟨190545460662814847656211933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127030307108543231770807955 190545460662814847656211933)
          ·
            refine ⟨71454547748555567871079475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190545460662814847656211933 71454547748555567871079475)
            ·
              refine ⟨107181821622833351806619213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71454547748555567871079475 107181821622833351806619213)
              ·
                refine ⟨40193183108562506927482205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107181821622833351806619213 40193183108562506927482205)
                ·
                  refine ⟨15072443665710940097805827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40193183108562506927482205 15072443665710940097805827)
                  ·
                    refine ⟨22608665498566410146708741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15072443665710940097805827 22608665498566410146708741)
                    ·
                      refine ⟨4239124780981201902507889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22608665498566410146708741 4239124780981201902507889)
                      ·
                        rfl

theorem cell23_8255666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_8255666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255666 prefixEnd_8255666 := by exact prefixLift 8255666
  have htrace : WordTrace (prefixWord ++ tailWord_8255666) baseStart_8255666 baseEnd_8255666 := by
    simpa [prefixWord, tailWord_8255666, baseEnd_8255666] using wordTrace_append hprefix tailTrace_8255666
  have hstable : (prefixWord ++ tailWord_8255666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255666).length < 2 ^ (prefixWord ++ tailWord_8255666).sum := by decide
  have hdescent : baseEnd_8255666 < baseStart_8255666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255679 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_8255679 : Nat := 118140960795 + 8255679 * 2 ^ 59
def prefixEnd_8255679 : Nat := 4983230072969 + 3 ^ 40 * 8255679 * 2
def baseEnd_8255679 : Nat := 4239131456229710351645329

theorem tailTrace_8255679 : CollatzResearch.WordTrace tailWord_8255679 prefixEnd_8255679 4239131456229710351645329 := by
  unfold tailWord_8255679
  simp only [CollatzResearch.WordTrace]
  refine ⟨301109350258092415565842091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200739566838728277043894727 301109350258092415565842091)
  ·
    refine ⟨451664025387138623348763137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301109350258092415565842091 451664025387138623348763137)
    ·
      refine ⟨338748019040353967511572353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451664025387138623348763137 338748019040353967511572353)
      ·
        refine ⟨254061014280265475633679265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338748019040353967511572353 254061014280265475633679265)
        ·
          refine ⟨190545760710199106725259449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254061014280265475633679265 190545760710199106725259449)
          ·
            refine ⟨142909320532649330043944587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190545760710199106725259449 142909320532649330043944587)
            ·
              refine ⟨214363980798973995065916881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142909320532649330043944587 214363980798973995065916881)
              ·
                refine ⟨160772985599230496299437661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214363980798973995065916881 160772985599230496299437661)
                ·
                  refine ⟨60289869599711436112289123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160772985599230496299437661 60289869599711436112289123)
                  ·
                    refine ⟨90434804399567154168433685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60289869599711436112289123 90434804399567154168433685)
                    ·
                      refine ⟨4239131456229710351645329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90434804399567154168433685 4239131456229710351645329)
                      ·
                        rfl

theorem cell23_8255679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_8255679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255679 prefixEnd_8255679 := by exact prefixLift 8255679
  have htrace : WordTrace (prefixWord ++ tailWord_8255679) baseStart_8255679 baseEnd_8255679 := by
    simpa [prefixWord, tailWord_8255679, baseEnd_8255679] using wordTrace_append hprefix tailTrace_8255679
  have hstable : (prefixWord ++ tailWord_8255679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255679).length < 2 ^ (prefixWord ++ tailWord_8255679).sum := by decide
  have hdescent : baseEnd_8255679 < baseStart_8255679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255680 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_8255680 : Nat := 118140960795 + 8255680 * 2 ^ 59
def prefixEnd_8255680 : Nat := 4983230072969 + 3 ^ 40 * 8255680 * 2
def baseEnd_8255680 : Nat := 1413043989903454949244275

theorem tailTrace_8255680 : CollatzResearch.WordTrace tailWord_8255680 prefixEnd_8255680 1413043989903454949244275 := by
  unfold tailWord_8255680
  simp only [CollatzResearch.WordTrace]
  refine ⟨150554693365544396368314247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200739591154059195157752329 150554693365544396368314247)
  ·
    refine ⟨225832040048316594552471371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150554693365544396368314247 225832040048316594552471371)
    ·
      refine ⟨338748060072474891828707057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225832040048316594552471371 338748060072474891828707057)
      ·
        refine ⟨254061045054356168871530293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338748060072474891828707057 254061045054356168871530293)
        ·
          refine ⟨23818222973845890831705965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254061045054356168871530293 23818222973845890831705965)
          ·
            refine ⟨8931833615192209061889737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23818222973845890831705965 8931833615192209061889737)
            ·
              refine ⟨6698875211394156796417303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8931833615192209061889737 6698875211394156796417303)
              ·
                refine ⟨10048312817091235194625955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698875211394156796417303 10048312817091235194625955)
                ·
                  refine ⟨15072469225636852791938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048312817091235194625955 15072469225636852791938933)
                  ·
                    refine ⟨1413043989903454949244275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15072469225636852791938933 1413043989903454949244275)
                    ·
                      rfl

theorem cell23_8255680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_8255680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255680 prefixEnd_8255680 := by exact prefixLift 8255680
  have htrace : WordTrace (prefixWord ++ tailWord_8255680) baseStart_8255680 baseEnd_8255680 := by
    simpa [prefixWord, tailWord_8255680, baseEnd_8255680] using wordTrace_append hprefix tailTrace_8255680
  have hstable : (prefixWord ++ tailWord_8255680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255680).length < 2 ^ (prefixWord ++ tailWord_8255680).sum := by decide
  have hdescent : baseEnd_8255680 < baseStart_8255680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255714 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8255714 : Nat := 118140960795 + 8255714 * 2 ^ 59
def prefixEnd_8255714 : Nat := 4983230072969 + 3 ^ 40 * 8255714 * 2
def baseEnd_8255714 : Nat := 1413049809350872571569223

theorem tailTrace_8255714 : CollatzResearch.WordTrace tailWord_8255714 prefixEnd_8255714 1413049809350872571569223 := by
  unfold tailWord_8255714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75277656703241404135841549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200740417875310411028910797 75277656703241404135841549)
  ·
    refine ⟨28229121263715526550940581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75277656703241404135841549 28229121263715526550940581)
    ·
      refine ⟨5292960236946661228301359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28229121263715526550940581 5292960236946661228301359)
      ·
        refine ⟨7939440355419991842452039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292960236946661228301359 7939440355419991842452039)
        ·
          refine ⟨11909160533129987763678059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939440355419991842452039 11909160533129987763678059)
          ·
            refine ⟨17863740799694981645517089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11909160533129987763678059 17863740799694981645517089)
            ·
              refine ⟨13397805599771236234137817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863740799694981645517089 13397805599771236234137817)
              ·
                refine ⟨10048354199828427175603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13397805599771236234137817 10048354199828427175603363)
                ·
                  refine ⟨15072531299742640763405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048354199828427175603363 15072531299742640763405045)
                  ·
                    refine ⟨1413049809350872571569223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15072531299742640763405045 1413049809350872571569223)
                    ·
                      rfl

theorem cell23_8255714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8255714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255714 prefixEnd_8255714 := by exact prefixLift 8255714
  have htrace : WordTrace (prefixWord ++ tailWord_8255714) baseStart_8255714 baseEnd_8255714 := by
    simpa [prefixWord, tailWord_8255714, baseEnd_8255714] using wordTrace_append hprefix tailTrace_8255714
  have hstable : (prefixWord ++ tailWord_8255714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255714).length < 2 ^ (prefixWord ++ tailWord_8255714).sum := by decide
  have hdescent : baseEnd_8255714 < baseStart_8255714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255720 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_8255720 : Nat := 118140960795 + 8255720 * 2 ^ 59
def prefixEnd_8255720 : Nat := 4983230072969 + 3 ^ 40 * 8255720 * 2
def baseEnd_8255720 : Nat := 4239152508936544691232641

theorem tailTrace_8255720 : CollatzResearch.WordTrace tailWord_8255720 prefixEnd_8255720 4239152508936544691232641 := by
  unfold tailWord_8255720
  simp only [CollatzResearch.WordTrace]
  refine ⟨150555422825471939784042307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200740563767295919712056409 150555422825471939784042307)
  ·
    refine ⟨225833134238207909676063461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150555422825471939784042307 225833134238207909676063461)
    ·
      refine ⟨42343712669663983064261899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225833134238207909676063461 42343712669663983064261899)
      ·
        refine ⟨63515569004495974596392849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42343712669663983064261899 63515569004495974596392849)
        ·
          refine ⟨47636676753371980947294637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63515569004495974596392849 47636676753371980947294637)
          ·
            refine ⟨17863753782514492855235489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47636676753371980947294637 17863753782514492855235489)
            ·
              refine ⟨13397815336885869641426617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863753782514492855235489 13397815336885869641426617)
              ·
                refine ⟨10048361502664402231069963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13397815336885869641426617 10048361502664402231069963)
                ·
                  refine ⟨15072542253996603346604945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048361502664402231069963 15072542253996603346604945)
                  ·
                    refine ⟨11304406690497452509953709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15072542253996603346604945 11304406690497452509953709)
                    ·
                      refine ⟨4239152508936544691232641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304406690497452509953709 4239152508936544691232641)
                      ·
                        rfl

theorem cell23_8255720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_8255720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255720 prefixEnd_8255720 := by exact prefixLift 8255720
  have htrace : WordTrace (prefixWord ++ tailWord_8255720) baseStart_8255720 baseEnd_8255720 := by
    simpa [prefixWord, tailWord_8255720, baseEnd_8255720] using wordTrace_append hprefix tailTrace_8255720
  have hstable : (prefixWord ++ tailWord_8255720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255720).length < 2 ^ (prefixWord ++ tailWord_8255720).sum := by decide
  have hdescent : baseEnd_8255720 < baseStart_8255720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255734 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_8255734 : Nat := 118140960795 + 8255734 * 2 ^ 59
def prefixEnd_8255734 : Nat := 4983230072969 + 3 ^ 40 * 8255734 * 2
def baseEnd_8255734 : Nat := 4239159697665707636457577

theorem tailTrace_8255734 : CollatzResearch.WordTrace tailWord_8255734 prefixEnd_8255734 4239159697665707636457577 := by
  unfold tailWord_8255734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819459767055822497443391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200740904181928773306062837 18819459767055822497443391)
  ·
    refine ⟨28229189650583733746165087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18819459767055822497443391 28229189650583733746165087)
    ·
      refine ⟨42343784475875600619247631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28229189650583733746165087 42343784475875600619247631)
      ·
        refine ⟨63515676713813400928871447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42343784475875600619247631 63515676713813400928871447)
        ·
          refine ⟨95273515070720101393307171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63515676713813400928871447 95273515070720101393307171)
          ·
            refine ⟨142910272606080152089960757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95273515070720101393307171 142910272606080152089960757)
            ·
              refine ⟨13397838056820014258433821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142910272606080152089960757 13397838056820014258433821)
              ·
                refine ⟨5024189271307505346912683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13397838056820014258433821 5024189271307505346912683)
                ·
                  refine ⟨7536283906961258020369025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024189271307505346912683 7536283906961258020369025)
                  ·
                    refine ⟨5652212930220943515276769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536283906961258020369025 5652212930220943515276769)
                    ·
                      refine ⟨4239159697665707636457577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652212930220943515276769 4239159697665707636457577)
                      ·
                        rfl

theorem cell23_8255734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_8255734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255734 prefixEnd_8255734 := by exact prefixLift 8255734
  have htrace : WordTrace (prefixWord ++ tailWord_8255734) baseStart_8255734 baseEnd_8255734 := by
    simpa [prefixWord, tailWord_8255734, baseEnd_8255734] using wordTrace_append hprefix tailTrace_8255734
  have hstable : (prefixWord ++ tailWord_8255734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255734).length < 2 ^ (prefixWord ++ tailWord_8255734).sum := by decide
  have hdescent : baseEnd_8255734 < baseStart_8255734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255739 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_8255739 : Nat := 118140960795 + 8255739 * 2 ^ 59
def prefixEnd_8255739 : Nat := 4983230072969 + 3 ^ 40 * 8255739 * 2
def baseEnd_8255739 : Nat := 4239162265068980116895053

theorem tailTrace_8255739 : CollatzResearch.WordTrace tailWord_8255739 prefixEnd_8255739 4239162265068980116895053 := by
  unfold tailWord_8255739
  simp only [CollatzResearch.WordTrace]
  refine ⟨301111538637875045813026271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200741025758583363875350847 301111538637875045813026271)
  ·
    refine ⟨451667307956812568719539407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301111538637875045813026271 451667307956812568719539407)
    ·
      refine ⟨677500961935218853079309111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451667307956812568719539407 677500961935218853079309111)
      ·
        refine ⟨1016251442902828279618963667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677500961935218853079309111 1016251442902828279618963667)
        ·
          refine ⟨1524377164354242419428445501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016251442902828279618963667 1524377164354242419428445501)
          ·
            refine ⟨571641436632840907285667063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1524377164354242419428445501 571641436632840907285667063)
            ·
              refine ⟨857462154949261360928500595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571641436632840907285667063 857462154949261360928500595)
              ·
                refine ⟨1286193232423892041392750893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857462154949261360928500595 1286193232423892041392750893)
                ·
                  refine ⟨482322462158959515522281585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1286193232423892041392750893 482322462158959515522281585)
                  ·
                    refine ⟨361741846619219636641711189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482322462158959515522281585 361741846619219636641711189)
                    ·
                      refine ⟨4239162265068980116895053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 361741846619219636641711189 4239162265068980116895053)
                      ·
                        rfl

theorem cell23_8255739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_8255739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255739 prefixEnd_8255739 := by exact prefixLift 8255739
  have htrace : WordTrace (prefixWord ++ tailWord_8255739) baseStart_8255739 baseEnd_8255739 := by
    simpa [prefixWord, tailWord_8255739, baseEnd_8255739] using wordTrace_append hprefix tailTrace_8255739
  have hstable : (prefixWord ++ tailWord_8255739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255739).length < 2 ^ (prefixWord ++ tailWord_8255739).sum := by decide
  have hdescent : baseEnd_8255739 < baseStart_8255739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255751 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8255751 : Nat := 118140960795 + 8255751 * 2 ^ 59
def prefixEnd_8255751 : Nat := 4983230072969 + 3 ^ 40 * 8255751 * 2
def baseEnd_8255751 : Nat := 4239168426836834069944999

theorem tailTrace_8255751 : CollatzResearch.WordTrace tailWord_8255751 prefixEnd_8255751 4239168426836834069944999 := by
  unfold tailWord_8255751
  simp only [CollatzResearch.WordTrace]
  refine ⟨301111976313831571862463107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200741317542554381241642071 301111976313831571862463107)
  ·
    refine ⟨451667964470747357793694661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301111976313831571862463107 451667964470747357793694661)
    ·
      refine ⟨84687743338265129586317749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451667964470747357793694661 84687743338265129586317749)
      ·
        refine ⟨7939475937962355898717289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84687743338265129586317749 7939475937962355898717289)
        ·
          refine ⟨5954606953471766924037967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939475937962355898717289 5954606953471766924037967)
          ·
            refine ⟨8931910430207650386056951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954606953471766924037967 8931910430207650386056951)
            ·
              refine ⟨13397865645311475579085427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931910430207650386056951 13397865645311475579085427)
              ·
                refine ⟨20096798467967213368628141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397865645311475579085427 20096798467967213368628141)
                ·
                  refine ⟨7536299425487705013235553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20096798467967213368628141 7536299425487705013235553)
                  ·
                    refine ⟨5652224569115778759926665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536299425487705013235553 5652224569115778759926665)
                    ·
                      refine ⟨4239168426836834069944999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652224569115778759926665 4239168426836834069944999)
                      ·
                        rfl

theorem cell23_8255751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8255751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255751 prefixEnd_8255751 := by exact prefixLift 8255751
  have htrace : WordTrace (prefixWord ++ tailWord_8255751) baseStart_8255751 baseEnd_8255751 := by
    simpa [prefixWord, tailWord_8255751, baseEnd_8255751] using wordTrace_append hprefix tailTrace_8255751
  have hstable : (prefixWord ++ tailWord_8255751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255751).length < 2 ^ (prefixWord ++ tailWord_8255751).sum := by decide
  have hdescent : baseEnd_8255751 < baseStart_8255751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255756 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_8255756 : Nat := 118140960795 + 8255756 * 2 ^ 59
def prefixEnd_8255756 : Nat := 4983230072969 + 3 ^ 40 * 8255756 * 2
def baseEnd_8255756 : Nat := 4239170994240106550382475

theorem tailTrace_8255756 : CollatzResearch.WordTrace tailWord_8255756 prefixEnd_8255756 4239170994240106550382475 := by
  unfold tailWord_8255756
  simp only [CollatzResearch.WordTrace]
  refine ⟨150556079339406728858197561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200741439119208971810930081 150556079339406728858197561)
  ·
    refine ⟨112917059504555046643648171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150556079339406728858197561 112917059504555046643648171)
    ·
      refine ⟨169375589256832569965472257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112917059504555046643648171 169375589256832569965472257)
      ·
        refine ⟨127031691942624427474104193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169375589256832569965472257 127031691942624427474104193)
        ·
          refine ⟨95273768956968320605578145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127031691942624427474104193 95273768956968320605578145)
          ·
            refine ⟨71455326717726240454183609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95273768956968320605578145 71455326717726240454183609)
            ·
              refine ⟨53591495038294680340637707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71455326717726240454183609 53591495038294680340637707)
              ·
                refine ⟨80387242557442020510956561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53591495038294680340637707 80387242557442020510956561)
                ·
                  refine ⟨60290431918081515383217421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80387242557442020510956561 60290431918081515383217421)
                  ·
                    refine ⟨22608911969280568268706533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60290431918081515383217421 22608911969280568268706533)
                    ·
                      refine ⟨4239170994240106550382475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22608911969280568268706533 4239170994240106550382475)
                      ·
                        rfl

theorem cell23_8255756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_8255756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255756 prefixEnd_8255756 := by exact prefixLift 8255756
  have htrace : WordTrace (prefixWord ++ tailWord_8255756) baseStart_8255756 baseEnd_8255756 := by
    simpa [prefixWord, tailWord_8255756, baseEnd_8255756] using wordTrace_append hprefix tailTrace_8255756
  have hstable : (prefixWord ++ tailWord_8255756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255756).length < 2 ^ (prefixWord ++ tailWord_8255756).sum := by decide
  have hdescent : baseEnd_8255756 < baseStart_8255756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255767 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_8255767 : Nat := 118140960795 + 8255767 * 2 ^ 59
def prefixEnd_8255767 : Nat := 4983230072969 + 3 ^ 40 * 8255767 * 2
def baseEnd_8255767 : Nat := 4239176642527306007344925

theorem tailTrace_8255767 : CollatzResearch.WordTrace tailWord_8255767 prefixEnd_8255767 4239176642527306007344925 := by
  unfold tailWord_8255767
  simp only [CollatzResearch.WordTrace]
  refine ⟨301112559881773606595045555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200741706587849071063363703 301112559881773606595045555)
  ·
    refine ⟨451668839822660409892568333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301112559881773606595045555 451668839822660409892568333)
    ·
      refine ⟨169375814933497653709713125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451668839822660409892568333 169375814933497653709713125)
      ·
        refine ⟨31757965300030810070571211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169375814933497653709713125 31757965300030810070571211)
        ·
          refine ⟨47636947950046215105856817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31757965300030810070571211 47636947950046215105856817)
          ·
            refine ⟨35727710962534661329392613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47636947950046215105856817 35727710962534661329392613)
            ·
              refine ⟨6698945805475248999261115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35727710962534661329392613 6698945805475248999261115)
              ·
                refine ⟨10048418708212873498891673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698945805475248999261115 10048418708212873498891673)
                ·
                  refine ⟨7536314031159655124168755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10048418708212873498891673 7536314031159655124168755)
                  ·
                    refine ⟨11304471046739482686253133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7536314031159655124168755 11304471046739482686253133)
                    ·
                      refine ⟨4239176642527306007344925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304471046739482686253133 4239176642527306007344925)
                      ·
                        rfl

theorem cell23_8255767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_8255767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255767 prefixEnd_8255767 := by exact prefixLift 8255767
  have htrace : WordTrace (prefixWord ++ tailWord_8255767) baseStart_8255767 baseEnd_8255767 := by
    simpa [prefixWord, tailWord_8255767, baseEnd_8255767] using wordTrace_append hprefix tailTrace_8255767
  have hstable : (prefixWord ++ tailWord_8255767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255767).length < 2 ^ (prefixWord ++ tailWord_8255767).sum := by decide
  have hdescent : baseEnd_8255767 < baseStart_8255767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255794 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_8255794 : Nat := 118140960795 + 8255794 * 2 ^ 59
def prefixEnd_8255794 : Nat := 4983230072969 + 3 ^ 40 * 8255794 * 2
def baseEnd_8255794 : Nat := 4239190506504977401707301

theorem tailTrace_8255794 : CollatzResearch.WordTrace tailWord_8255794 prefixEnd_8255794 4239190506504977401707301 := by
  unfold tailWord_8255794
  simp only [CollatzResearch.WordTrace]
  refine ⟨75278386163168947551569609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200742363101783860137518957 75278386163168947551569609)
  ·
    refine ⟨56458789622376710663677207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75278386163168947551569609 56458789622376710663677207)
    ·
      refine ⟨84688184433565065995515811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56458789622376710663677207 84688184433565065995515811)
      ·
        refine ⟨127032276650347598993273717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84688184433565065995515811 127032276650347598993273717)
        ·
          refine ⟨11909275935970087405619411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127032276650347598993273717 11909275935970087405619411)
          ·
            refine ⟨17863913903955131108429117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11909275935970087405619411 17863913903955131108429117)
            ·
              refine ⟨6698967713983174165660919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17863913903955131108429117 6698967713983174165660919)
              ·
                refine ⟨10048451570974761248491379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698967713983174165660919 10048451570974761248491379)
                ·
                  refine ⟨15072677356462141872737069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048451570974761248491379 15072677356462141872737069)
                  ·
                    refine ⟨5652254008673303202276401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15072677356462141872737069 5652254008673303202276401)
                    ·
                      refine ⟨4239190506504977401707301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652254008673303202276401 4239190506504977401707301)
                      ·
                        rfl

theorem cell23_8255794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_8255794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255794 prefixEnd_8255794 := by exact prefixLift 8255794
  have htrace : WordTrace (prefixWord ++ tailWord_8255794) baseStart_8255794 baseEnd_8255794 := by
    simpa [prefixWord, tailWord_8255794, baseEnd_8255794] using wordTrace_append hprefix tailTrace_8255794
  have hstable : (prefixWord ++ tailWord_8255794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255794).length < 2 ^ (prefixWord ++ tailWord_8255794).sum := by decide
  have hdescent : baseEnd_8255794 < baseStart_8255794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255807 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 2, 2, 2]
def baseStart_8255807 : Nat := 118140960795 + 8255807 * 2 ^ 59
def prefixEnd_8255807 : Nat := 4983230072969 + 3 ^ 40 * 8255807 * 2
def baseEnd_8255807 : Nat := 4239197181753485850844741

theorem tailTrace_8255807 : CollatzResearch.WordTrace tailWord_8255807 prefixEnd_8255807 4239197181753485850844741 := by
  unfold tailWord_8255807
  simp only [CollatzResearch.WordTrace]
  refine ⟨301114018801628693426501675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200742679201085795617667783 301114018801628693426501675)
  ·
    refine ⟨451671028202443040139752513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301114018801628693426501675 451671028202443040139752513)
    ·
      refine ⟨338753271151832280104814385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451671028202443040139752513 338753271151832280104814385)
      ·
        refine ⟨254064953363874210078610789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338753271151832280104814385 254064953363874210078610789)
        ·
          refine ⟨47637178755726414389739523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254064953363874210078610789 47637178755726414389739523)
          ·
            refine ⟨71455768133589621584609285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47637178755726414389739523 71455768133589621584609285)
            ·
              refine ⟨13397956525048054047114241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71455768133589621584609285 13397956525048054047114241)
              ·
                refine ⟨10048467393786040535335681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13397956525048054047114241 10048467393786040535335681)
                ·
                  refine ⟨7536350545339530401501761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10048467393786040535335681 7536350545339530401501761)
                  ·
                    refine ⟨5652262909004647801126321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536350545339530401501761 5652262909004647801126321)
                    ·
                      refine ⟨4239197181753485850844741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652262909004647801126321 4239197181753485850844741)
                      ·
                        rfl

theorem cell23_8255807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_8255807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255807 prefixEnd_8255807 := by exact prefixLift 8255807
  have htrace : WordTrace (prefixWord ++ tailWord_8255807) baseStart_8255807 baseEnd_8255807 := by
    simpa [prefixWord, tailWord_8255807, baseEnd_8255807] using wordTrace_append hprefix tailTrace_8255807
  have hstable : (prefixWord ++ tailWord_8255807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255807).length < 2 ^ (prefixWord ++ tailWord_8255807).sum := by decide
  have hdescent : baseEnd_8255807 < baseStart_8255807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255833 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 5, 2]
def baseStart_8255833 : Nat := 118140960795 + 8255833 * 2 ^ 59
def prefixEnd_8255833 : Nat := 4983230072969 + 3 ^ 40 * 8255833 * 2
def baseEnd_8255833 : Nat := 4239210532250502749119621

theorem tailTrace_8255833 : CollatzResearch.WordTrace tailWord_8255833 prefixEnd_8255833 4239210532250502749119621 := by
  unfold tailWord_8255833
  simp only [CollatzResearch.WordTrace]
  refine ⟨301114967099534499866948153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200743311399689666577965435 301114967099534499866948153)
  ·
    refine ⟨225836225324650874900211115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301114967099534499866948153 225836225324650874900211115)
    ·
      refine ⟨338754337986976312350316673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225836225324650874900211115 338754337986976312350316673)
      ·
        refine ⟨254065753490232234262737505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338754337986976312350316673 254065753490232234262737505)
        ·
          refine ⟨190549315117674175697053129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254065753490232234262737505 190549315117674175697053129)
          ·
            refine ⟨142911986338255631772789847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190549315117674175697053129 142911986338255631772789847)
            ·
              refine ⟨214367979507383447659184771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142911986338255631772789847 214367979507383447659184771)
              ·
                refine ⟨321551969261075171488777157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214367979507383447659184771 321551969261075171488777157)
                ·
                  refine ⟨60290994236451594654145717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321551969261075171488777157 60290994236451594654145717)
                  ·
                    refine ⟨5652280709667336998826161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60290994236451594654145717 5652280709667336998826161)
                    ·
                      refine ⟨4239210532250502749119621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652280709667336998826161 4239210532250502749119621)
                      ·
                        rfl

theorem cell23_8255833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_8255833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255833 prefixEnd_8255833 := by exact prefixLift 8255833
  have htrace : WordTrace (prefixWord ++ tailWord_8255833) baseStart_8255833 baseEnd_8255833 := by
    simpa [prefixWord, tailWord_8255833, baseEnd_8255833] using wordTrace_append hprefix tailTrace_8255833
  have hstable : (prefixWord ++ tailWord_8255833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255833).length < 2 ^ (prefixWord ++ tailWord_8255833).sum := by decide
  have hdescent : baseEnd_8255833 < baseStart_8255833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255880 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_8255880 : Nat := 118140960795 + 8255880 * 2 ^ 59
def prefixEnd_8255880 : Nat := 4983230072969 + 3 ^ 40 * 8255880 * 2
def baseEnd_8255880 : Nat := 4239234665841264065231905

theorem tailTrace_8255880 : CollatzResearch.WordTrace tailWord_8255880 prefixEnd_8255880 4239234665841264065231905 := by
  unfold tailWord_8255880
  simp only [CollatzResearch.WordTrace]
  refine ⟨150558340665182113446954547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200744454220242817929272729 150558340665182113446954547)
  ·
    refine ⟨225837510997773170170431821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150558340665182113446954547 225837510997773170170431821)
    ·
      refine ⟨84689066624164938813911933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225837510997773170170431821 84689066624164938813911933)
      ·
        refine ⟨31758399984061852055216975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84689066624164938813911933 31758399984061852055216975)
        ·
          refine ⟨47637599976092778082825463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31758399984061852055216975 47637599976092778082825463)
          ·
            refine ⟨71456399964139167124238195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47637599976092778082825463 71456399964139167124238195)
            ·
              refine ⟨107184599946208750686357293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71456399964139167124238195 107184599946208750686357293)
              ·
                refine ⟨40194224979828281507383985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107184599946208750686357293 40194224979828281507383985)
                ·
                  refine ⟨30145668734871211130537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40194224979828281507383985 30145668734871211130537989)
                  ·
                    refine ⟨5652312887788352086975873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30145668734871211130537989 5652312887788352086975873)
                    ·
                      refine ⟨4239234665841264065231905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652312887788352086975873 4239234665841264065231905)
                      ·
                        rfl

theorem cell23_8255880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_8255880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255880 prefixEnd_8255880 := by exact prefixLift 8255880
  have htrace : WordTrace (prefixWord ++ tailWord_8255880) baseStart_8255880 baseEnd_8255880 := by
    simpa [prefixWord, tailWord_8255880, baseEnd_8255880] using wordTrace_append hprefix tailTrace_8255880
  have hstable : (prefixWord ++ tailWord_8255880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255880).length < 2 ^ (prefixWord ++ tailWord_8255880).sum := by decide
  have hdescent : baseEnd_8255880 < baseStart_8255880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255883 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3]
def baseStart_8255883 : Nat := 118140960795 + 8255883 * 2 ^ 59
def prefixEnd_8255883 : Nat := 4983230072969 + 3 ^ 40 * 8255883 * 2
def baseEnd_8255883 : Nat := 4239236206283227553494391

theorem tailTrace_8255883 : CollatzResearch.WordTrace tailWord_8255883 prefixEnd_8255883 4239236206283227553494391 := by
  unfold tailWord_8255883
  simp only [CollatzResearch.WordTrace]
  refine ⟨301116790749353358406268303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200744527166235572270845535 301116790749353358406268303)
  ·
    refine ⟨451675186124030037609402455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301116790749353358406268303 451675186124030037609402455)
    ·
      refine ⟨677512779186045056414103683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451675186124030037609402455 677512779186045056414103683)
      ·
        refine ⟨1016269168779067584621155525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677512779186045056414103683 1016269168779067584621155525)
        ·
          refine ⟨190550469146075172116466661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016269168779067584621155525 190550469146075172116466661)
          ·
            refine ⟨35728212964889094771837499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190550469146075172116466661 35728212964889094771837499)
            ·
              refine ⟨53592319447333642157756249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35728212964889094771837499 53592319447333642157756249)
              ·
                refine ⟨40194239585500231618317187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53592319447333642157756249 40194239585500231618317187)
                ·
                  refine ⟨60291359378250347427475781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40194239585500231618317187 60291359378250347427475781)
                  ·
                    refine ⟨11304629883421940142651709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60291359378250347427475781 11304629883421940142651709)
                    ·
                      refine ⟨4239236206283227553494391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304629883421940142651709 4239236206283227553494391)
                      ·
                        rfl

theorem cell23_8255883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].length) (baseStart_8255883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255883 prefixEnd_8255883 := by exact prefixLift 8255883
  have htrace : WordTrace (prefixWord ++ tailWord_8255883) baseStart_8255883 baseEnd_8255883 := by
    simpa [prefixWord, tailWord_8255883, baseEnd_8255883] using wordTrace_append hprefix tailTrace_8255883
  have hstable : (prefixWord ++ tailWord_8255883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255883).length < 2 ^ (prefixWord ++ tailWord_8255883).sum := by decide
  have hdescent : baseEnd_8255883 < baseStart_8255883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255907 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 1, 4]
def baseStart_8255907 : Nat := 118140960795 + 8255907 * 2 ^ 59
def prefixEnd_8255907 : Nat := 4983230072969 + 3 ^ 40 * 8255907 * 2
def baseEnd_8255907 : Nat := 1413082843272978486531427

theorem tailTrace_8255907 : CollatzResearch.WordTrace tailWord_8255907 prefixEnd_8255907 1413082843272978486531427 := by
  unfold tailWord_8255907
  simp only [CollatzResearch.WordTrace]
  refine ⟨301117666101266410505141975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200745110734177607003427983 301117666101266410505141975)
  ·
    refine ⟨451676499151899615757712963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301117666101266410505141975 451676499151899615757712963)
    ·
      refine ⟨677514748727849423636569445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451676499151899615757712963 677514748727849423636569445)
      ·
        refine ⟨127034015386471766931856771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677514748727849423636569445 127034015386471766931856771)
        ·
          refine ⟨190551023079707650397785157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127034015386471766931856771 190551023079707650397785157)
          ·
            refine ⟨35728316827445184449584717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190551023079707650397785157 35728316827445184449584717)
            ·
              refine ⟨13398118810291944168594269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35728316827445184449584717 13398118810291944168594269)
              ·
                refine ⟨5024294553859479063222851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13398118810291944168594269 5024294553859479063222851)
                ·
                  refine ⟨7536441830789218594834277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024294553859479063222851 7536441830789218594834277)
                  ·
                    refine ⟨1413082843272978486531427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536441830789218594834277 1413082843272978486531427)
                    ·
                      rfl

theorem cell23_8255907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 4].length) (baseStart_8255907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255907 prefixEnd_8255907 := by exact prefixLift 8255907
  have htrace : WordTrace (prefixWord ++ tailWord_8255907) baseStart_8255907 baseEnd_8255907 := by
    simpa [prefixWord, tailWord_8255907, baseEnd_8255907] using wordTrace_append hprefix tailTrace_8255907
  have hstable : (prefixWord ++ tailWord_8255907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255907).length < 2 ^ (prefixWord ++ tailWord_8255907).sum := by decide
  have hdescent : baseEnd_8255907 < baseStart_8255907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255957 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_8255957 : Nat := 118140960795 + 8255957 * 2 ^ 59
def prefixEnd_8255957 : Nat := 4983230072969 + 3 ^ 40 * 8255957 * 2
def baseEnd_8255957 : Nat := 4239274203851660263969051

theorem tailTrace_8255957 : CollatzResearch.WordTrace tailWord_8255957 prefixEnd_8255957 4239274203851660263969051 := by
  unfold tailWord_8255957
  simp only [CollatzResearch.WordTrace]
  refine ⟨301119489751085269044462125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200746326500723512696308083 301119489751085269044462125)
  ·
    refine ⟨112919808656656975891673297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301119489751085269044462125 112919808656656975891673297)
    ·
      refine ⟨84689856492492731918754973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112919808656656975891673297 84689856492492731918754973)
      ·
        refine ⟨31758696184684774469533115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84689856492492731918754973 31758696184684774469533115)
        ·
          refine ⟨47638044277027161704299673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31758696184684774469533115 47638044277027161704299673)
          ·
            refine ⟨35728533207770371278224755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47638044277027161704299673 35728533207770371278224755)
            ·
              refine ⟨53592799811655556917337133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35728533207770371278224755 53592799811655556917337133)
              ·
                refine ⟨20097299929370833844001425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53592799811655556917337133 20097299929370833844001425)
                ·
                  refine ⟨15072974947028125383001069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20097299929370833844001425 15072974947028125383001069)
                  ·
                    refine ⟨5652365605135547018625401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15072974947028125383001069 5652365605135547018625401)
                    ·
                      refine ⟨4239274203851660263969051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652365605135547018625401 4239274203851660263969051)
                      ·
                        rfl

theorem cell23_8255957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_8255957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255957 prefixEnd_8255957 := by exact prefixLift 8255957
  have htrace : WordTrace (prefixWord ++ tailWord_8255957) baseStart_8255957 baseEnd_8255957 := by
    simpa [prefixWord, tailWord_8255957, baseEnd_8255957] using wordTrace_append hprefix tailTrace_8255957
  have hstable : (prefixWord ++ tailWord_8255957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255957).length < 2 ^ (prefixWord ++ tailWord_8255957).sum := by decide
  have hdescent : baseEnd_8255957 < baseStart_8255957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255967 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 1, 5]
def baseStart_8255967 : Nat := 118140960795 + 8255967 * 2 ^ 59
def prefixEnd_8255967 : Nat := 4983230072969 + 3 ^ 40 * 8255967 * 2
def baseEnd_8255967 : Nat := 1413093112886068408281335

theorem tailTrace_8255967 : CollatzResearch.WordTrace tailWord_8255967 prefixEnd_8255967 1413093112886068408281335 := by
  unfold tailWord_8255967
  simp only [CollatzResearch.WordTrace]
  refine ⟨301119854481049040752326155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200746569654032693834884103 301119854481049040752326155)
  ·
    refine ⟨451679781721573561128489233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301119854481049040752326155 451679781721573561128489233)
    ·
      refine ⟨338759836291180170846366925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451679781721573561128489233 338759836291180170846366925)
      ·
        refine ⟨127034938609192564067387597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338759836291180170846366925 127034938609192564067387597)
        ·
          refine ⟨47638101978447211525270349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127034938609192564067387597 47638101978447211525270349)
          ·
            refine ⟨17864288241917704321976381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47638101978447211525270349 17864288241917704321976381)
            ·
              refine ⟨6699108090719139120741143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17864288241917704321976381 6699108090719139120741143)
              ·
                refine ⟨10048662136078708681111715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699108090719139120741143 10048662136078708681111715)
                ·
                  refine ⟨15072993204118063021667573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048662136078708681111715 15072993204118063021667573)
                  ·
                    refine ⟨1413093112886068408281335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15072993204118063021667573 1413093112886068408281335)
                    ·
                      rfl

theorem cell23_8255967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_8255967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255967 prefixEnd_8255967 := by exact prefixLift 8255967
  have htrace : WordTrace (prefixWord ++ tailWord_8255967) baseStart_8255967 baseEnd_8255967 := by
    simpa [prefixWord, tailWord_8255967, baseEnd_8255967] using wordTrace_append hprefix tailTrace_8255967
  have hstable : (prefixWord ++ tailWord_8255967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255967).length < 2 ^ (prefixWord ++ tailWord_8255967).sum := by decide
  have hdescent : baseEnd_8255967 < baseStart_8255967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255981 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_8255981 : Nat := 118140960795 + 8255981 * 2 ^ 59
def prefixEnd_8255981 : Nat := 4983230072969 + 3 ^ 40 * 8255981 * 2
def baseEnd_8255981 : Nat := 4239286527387368170068941

theorem tailTrace_8255981 : CollatzResearch.WordTrace tailWord_8255981 prefixEnd_8255981 4239286527387368170068941 := by
  unfold tailWord_8255981
  simp only [CollatzResearch.WordTrace]
  refine ⟨301120365102998321143335797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200746910068665547428890531 301120365102998321143335797)
  ·
    refine ⟨28230034228406092607187731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301120365102998321143335797 28230034228406092607187731)
    ·
      refine ⟨42345051342609138910781597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230034228406092607187731 42345051342609138910781597)
      ·
        refine ⟨15879394253478427091543099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42345051342609138910781597 15879394253478427091543099)
        ·
          refine ⟨23819091380217640637314649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879394253478427091543099 23819091380217640637314649)
          ·
            refine ⟨17864318535163230477985987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23819091380217640637314649 17864318535163230477985987)
            ·
              refine ⟨26796477802744845716978981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17864318535163230477985987 26796477802744845716978981)
              ·
                refine ⟨5024339588014658571933559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26796477802744845716978981 5024339588014658571933559)
                ·
                  refine ⟨7536509382021987857900339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024339588014658571933559 7536509382021987857900339)
                  ·
                    refine ⟨11304764073032981786850509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7536509382021987857900339 11304764073032981786850509)
                    ·
                      refine ⟨4239286527387368170068941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304764073032981786850509 4239286527387368170068941)
                      ·
                        rfl

theorem cell23_8255981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_8255981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255981 prefixEnd_8255981 := by exact prefixLift 8255981
  have htrace : WordTrace (prefixWord ++ tailWord_8255981) baseStart_8255981 baseEnd_8255981 := by
    simpa [prefixWord, tailWord_8255981, baseEnd_8255981] using wordTrace_append hprefix tailTrace_8255981
  have hstable : (prefixWord ++ tailWord_8255981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255981).length < 2 ^ (prefixWord ++ tailWord_8255981).sum := by decide
  have hdescent : baseEnd_8255981 < baseStart_8255981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255983 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_8255983 : Nat := 118140960795 + 8255983 * 2 ^ 59
def prefixEnd_8255983 : Nat := 4983230072969 + 3 ^ 40 * 8255983 * 2
def baseEnd_8255983 : Nat := 4239287554348677162243931

theorem tailTrace_8255983 : CollatzResearch.WordTrace tailWord_8255983 prefixEnd_8255983 4239287554348677162243931 := by
  unfold tailWord_8255983
  simp only [CollatzResearch.WordTrace]
  refine ⟨301120438048991075484908603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200746958699327383656605735 301120438048991075484908603)
  ·
    refine ⟨451680657073486613227362905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301120438048991075484908603 451680657073486613227362905)
    ·
      refine ⟨338760492805114959920522179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451680657073486613227362905 338760492805114959920522179)
      ·
        refine ⟨508140739207672439880783269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338760492805114959920522179 508140739207672439880783269)
        ·
          refine ⟨95276388601438582477646863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508140739207672439880783269 95276388601438582477646863)
          ·
            refine ⟨142914582902157873716470295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95276388601438582477646863 142914582902157873716470295)
            ·
              refine ⟨214371874353236810574705443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142914582902157873716470295 214371874353236810574705443)
              ·
                refine ⟨321557811529855215862058165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214371874353236810574705443 321557811529855215862058165)
                ·
                  refine ⟨30146044830923926487067953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321557811529855215862058165 30146044830923926487067953)
                  ·
                    refine ⟨22609533623192944865300965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30146044830923926487067953 22609533623192944865300965)
                    ·
                      refine ⟨4239287554348677162243931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22609533623192944865300965 4239287554348677162243931)
                      ·
                        rfl

theorem cell23_8255983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_8255983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255983 prefixEnd_8255983 := by exact prefixLift 8255983
  have htrace : WordTrace (prefixWord ++ tailWord_8255983) baseStart_8255983 baseEnd_8255983 := by
    simpa [prefixWord, tailWord_8255983, baseEnd_8255983] using wordTrace_append hprefix tailTrace_8255983
  have hstable : (prefixWord ++ tailWord_8255983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255983).length < 2 ^ (prefixWord ++ tailWord_8255983).sum := by decide
  have hdescent : baseEnd_8255983 < baseStart_8255983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255987 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 3, 2, 2]
def baseStart_8255987 : Nat := 118140960795 + 8255987 * 2 ^ 59
def prefixEnd_8255987 : Nat := 4983230072969 + 3 ^ 40 * 8255987 * 2
def baseEnd_8255987 : Nat := 4239289608271295146593913

theorem tailTrace_8255987 : CollatzResearch.WordTrace tailWord_8255987 prefixEnd_8255987 4239289608271295146593913 := by
  unfold tailWord_8255987
  simp only [CollatzResearch.WordTrace]
  refine ⟨301120583940976584168054215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200747055960651056112036143 301120583940976584168054215)
  ·
    refine ⟨451680875911464876252081323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301120583940976584168054215 451680875911464876252081323)
    ·
      refine ⟨677521313867197314378121985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451680875911464876252081323 677521313867197314378121985)
      ·
        refine ⟨508140985400397985783591489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677521313867197314378121985 508140985400397985783591489)
        ·
          refine ⟨381105739050298489337693617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508140985400397985783591489 381105739050298489337693617)
          ·
            refine ⟨285829304287723867003270213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381105739050298489337693617 285829304287723867003270213)
            ·
              refine ⟨53592994553948225063113165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285829304287723867003270213 53592994553948225063113165)
              ·
                refine ⟨20097372957730584398667437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53592994553948225063113165 20097372957730584398667437)
                ·
                  refine ⟨7536514859148969149500289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20097372957730584398667437 7536514859148969149500289)
                  ·
                    refine ⟨5652386144361726862125217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536514859148969149500289 5652386144361726862125217)
                    ·
                      refine ⟨4239289608271295146593913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652386144361726862125217 4239289608271295146593913)
                      ·
                        rfl

theorem cell23_8255987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2, 2].length) (baseStart_8255987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255987 prefixEnd_8255987 := by exact prefixLift 8255987
  have htrace : WordTrace (prefixWord ++ tailWord_8255987) baseStart_8255987 baseEnd_8255987 := by
    simpa [prefixWord, tailWord_8255987, baseEnd_8255987] using wordTrace_append hprefix tailTrace_8255987
  have hstable : (prefixWord ++ tailWord_8255987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255987).length < 2 ^ (prefixWord ++ tailWord_8255987).sum := by decide
  have hdescent : baseEnd_8255987 < baseStart_8255987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255990 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_8255990 : Nat := 118140960795 + 8255990 * 2 ^ 59
def prefixEnd_8255990 : Nat := 4983230072969 + 3 ^ 40 * 8255990 * 2
def baseEnd_8255990 : Nat := 4239291148713258634856399

theorem tailTrace_8255990 : CollatzResearch.WordTrace tailWord_8255990 prefixEnd_8255990 4239291148713258634856399 := by
  unfold tailWord_8255990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820043334997857230025839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200747128906643810453608949 18820043334997857230025839)
  ·
    refine ⟨28230065002496785845038759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18820043334997857230025839 28230065002496785845038759)
    ·
      refine ⟨42345097503745178767558139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230065002496785845038759 42345097503745178767558139)
      ·
        refine ⟨63517646255617768151337209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42345097503745178767558139 63517646255617768151337209)
        ·
          refine ⟨47638234691713326113502907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63517646255617768151337209 47638234691713326113502907)
          ·
            refine ⟨71457352037569989170254361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47638234691713326113502907 71457352037569989170254361)
            ·
              refine ⟨53593014028177491877690771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71457352037569989170254361 53593014028177491877690771)
              ·
                refine ⟨80389521042266237816536157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53593014028177491877690771 80389521042266237816536157)
                ·
                  refine ⟨30146070390849839181201059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80389521042266237816536157 30146070390849839181201059)
                  ·
                    refine ⟨45219105586274758771801589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30146070390849839181201059 45219105586274758771801589)
                    ·
                      refine ⟨4239291148713258634856399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45219105586274758771801589 4239291148713258634856399)
                      ·
                        rfl

theorem cell23_8255990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_8255990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255990 prefixEnd_8255990 := by exact prefixLift 8255990
  have htrace : WordTrace (prefixWord ++ tailWord_8255990) baseStart_8255990 baseEnd_8255990 := by
    simpa [prefixWord, tailWord_8255990, baseEnd_8255990] using wordTrace_append hprefix tailTrace_8255990
  have hstable : (prefixWord ++ tailWord_8255990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255990).length < 2 ^ (prefixWord ++ tailWord_8255990).sum := by decide
  have hdescent : baseEnd_8255990 < baseStart_8255990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8255993 : List Nat := [1, 2, 1, 3, 1, 2, 5, 8]
def baseStart_8255993 : Nat := 118140960795 + 8255993 * 2 ^ 59
def prefixEnd_8255993 : Nat := 4983230072969 + 3 ^ 40 * 8255993 * 2
def baseEnd_8255993 : Nat := 157010840339082300856255

theorem tailTrace_8255993 : CollatzResearch.WordTrace tailWord_8255993 prefixEnd_8255993 157010840339082300856255 := by
  unfold tailWord_8255993
  simp only [CollatzResearch.WordTrace]
  refine ⟨301120802778954847192772633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200747201852636564795181755 301120802778954847192772633)
  ·
    refine ⟨225840602084216135394579475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301120802778954847192772633 225840602084216135394579475)
    ·
      refine ⟨338760903126324203091869213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225840602084216135394579475 338760903126324203091869213)
      ·
        refine ⟨127035338672371576159450955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338760903126324203091869213 127035338672371576159450955)
        ·
          refine ⟨190553008008557364239176433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127035338672371576159450955 190553008008557364239176433)
          ·
            refine ⟨142914756006418023179382325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190553008008557364239176433 142914756006418023179382325)
            ·
              refine ⟨13398258375601689673067093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142914756006418023179382325 13398258375601689673067093)
              ·
                refine ⟨157010840339082300856255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13398258375601689673067093 157010840339082300856255)
                ·
                  rfl

theorem cell23_8255993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 8].length) (baseStart_8255993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8255993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8255993 prefixEnd_8255993 := by exact prefixLift 8255993
  have htrace : WordTrace (prefixWord ++ tailWord_8255993) baseStart_8255993 baseEnd_8255993 := by
    simpa [prefixWord, tailWord_8255993, baseEnd_8255993] using wordTrace_append hprefix tailTrace_8255993
  have hstable : (prefixWord ++ tailWord_8255993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8255993).length < 2 ^ (prefixWord ++ tailWord_8255993).sum := by decide
  have hdescent : baseEnd_8255993 < baseStart_8255993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8255993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256004 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_8256004 : Nat := 118140960795 + 8256004 * 2 ^ 59
def prefixEnd_8256004 : Nat := 4983230072969 + 3 ^ 40 * 8256004 * 2
def baseEnd_8256004 : Nat := 4239298337442421580081335

theorem tailTrace_8256004 : CollatzResearch.WordTrace tailWord_8256004 prefixEnd_8256004 4239298337442421580081335 := by
  unfold tailWord_8256004
  simp only [CollatzResearch.WordTrace]
  refine ⟨150560601990957498035711533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200747469321276664047615377 150560601990957498035711533)
  ·
    refine ⟨56460225746609061763391825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150560601990957498035711533 56460225746609061763391825)
    ·
      refine ⟨42345169309956796322543869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56460225746609061763391825 42345169309956796322543869)
      ·
        refine ⟨15879438491233798620953951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42345169309956796322543869 15879438491233798620953951)
        ·
          refine ⟨23819157736850697931430927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879438491233798620953951 23819157736850697931430927)
          ·
            refine ⟨35728736605276046897146391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819157736850697931430927 35728736605276046897146391)
            ·
              refine ⟨53593104907914070345719587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35728736605276046897146391 53593104907914070345719587)
              ·
                refine ⟨80389657361871105518579381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53593104907914070345719587 80389657361871105518579381)
                ·
                  refine ⟨7536530377675416142366817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80389657361871105518579381 7536530377675416142366817)
                  ·
                    refine ⟨5652397783256562106775113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536530377675416142366817 5652397783256562106775113)
                    ·
                      refine ⟨4239298337442421580081335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652397783256562106775113 4239298337442421580081335)
                      ·
                        rfl

theorem cell23_8256004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_8256004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256004 prefixEnd_8256004 := by exact prefixLift 8256004
  have htrace : WordTrace (prefixWord ++ tailWord_8256004) baseStart_8256004 baseEnd_8256004 := by
    simpa [prefixWord, tailWord_8256004, baseEnd_8256004] using wordTrace_append hprefix tailTrace_8256004
  have hstable : (prefixWord ++ tailWord_8256004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256004).length < 2 ^ (prefixWord ++ tailWord_8256004).sum := by decide
  have hdescent : baseEnd_8256004 < baseStart_8256004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256010 : List Nat := [3, 1, 2, 2, 2, 1, 5, 7]
def baseStart_8256010 : Nat := 118140960795 + 8256010 * 2 ^ 59
def prefixEnd_8256010 : Nat := 4983230072969 + 3 ^ 40 * 8256010 * 2
def baseEnd_8256010 : Nat := 157011163641716613207641

theorem tailTrace_8256010 : CollatzResearch.WordTrace tailWord_8256010 prefixEnd_8256010 157011163641716613207641 := by
  unfold tailWord_8256010
  simp only [CollatzResearch.WordTrace]
  refine ⟨75280355704973314774035371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200747615213262172730760989 75280355704973314774035371)
  ·
    refine ⟨112920533557459972161053057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75280355704973314774035371 112920533557459972161053057)
    ·
      refine ⟨84690400168094979120789793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112920533557459972161053057 84690400168094979120789793)
      ·
        refine ⟨63517800126071234340592345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84690400168094979120789793 63517800126071234340592345)
        ·
          refine ⟨47638350094553425755444259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63517800126071234340592345 47638350094553425755444259)
          ·
            refine ⟨71457525141830138633166389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47638350094553425755444259 71457525141830138633166389)
            ·
              refine ⟨6699142982046575496859349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71457525141830138633166389 6699142982046575496859349)
              ·
                refine ⟨157011163641716613207641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6699142982046575496859349 157011163641716613207641)
                ·
                  rfl

theorem cell23_8256010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_8256010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256010 prefixEnd_8256010 := by exact prefixLift 8256010
  have htrace : WordTrace (prefixWord ++ tailWord_8256010) baseStart_8256010 baseEnd_8256010 := by
    simpa [prefixWord, tailWord_8256010, baseEnd_8256010] using wordTrace_append hprefix tailTrace_8256010
  have hstable : (prefixWord ++ tailWord_8256010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256010).length < 2 ^ (prefixWord ++ tailWord_8256010).sum := by decide
  have hdescent : baseEnd_8256010 < baseStart_8256010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256021 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_8256021 : Nat := 118140960795 + 8256021 * 2 ^ 59
def prefixEnd_8256021 : Nat := 4983230072969 + 3 ^ 40 * 8256021 * 2
def baseEnd_8256021 : Nat := 4239307066613548013568757

theorem tailTrace_8256021 : CollatzResearch.WordTrace tailWord_8256021 prefixEnd_8256021 4239307066613548013568757 := by
  unfold tailWord_8256021
  simp only [CollatzResearch.WordTrace]
  refine ⟨301121824022853407974791917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200747882681902271983194611 301121824022853407974791917)
  ·
    refine ⟨112920684008570027990546969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301121824022853407974791917 112920684008570027990546969)
    ·
      refine ⟨84690513006427520992910227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112920684008570027990546969 84690513006427520992910227)
      ·
        refine ⟨127035769509641281489365341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84690513006427520992910227 127035769509641281489365341)
        ·
          refine ⟨47638413566115480558512003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127035769509641281489365341 47638413566115480558512003)
          ·
            refine ⟨71457620349173220837768005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47638413566115480558512003 71457620349173220837768005)
            ·
              refine ⟨13398303815469978907081501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71457620349173220837768005 13398303815469978907081501)
              ·
                refine ⟨5024363930801242090155563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13398303815469978907081501 5024363930801242090155563)
                ·
                  refine ⟨7536545896201863135233345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024363930801242090155563 7536545896201863135233345)
                  ·
                    refine ⟨5652409422151397351425009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536545896201863135233345 5652409422151397351425009)
                    ·
                      refine ⟨4239307066613548013568757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652409422151397351425009 4239307066613548013568757)
                      ·
                        rfl

theorem cell23_8256021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_8256021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256021 prefixEnd_8256021 := by exact prefixLift 8256021
  have htrace : WordTrace (prefixWord ++ tailWord_8256021) baseStart_8256021 baseEnd_8256021 := by
    simpa [prefixWord, tailWord_8256021, baseEnd_8256021] using wordTrace_append hprefix tailTrace_8256021
  have hstable : (prefixWord ++ tailWord_8256021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256021).length < 2 ^ (prefixWord ++ tailWord_8256021).sum := by decide
  have hdescent : baseEnd_8256021 < baseStart_8256021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256024 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_8256024 : Nat := 118140960795 + 8256024 * 2 ^ 59
def prefixEnd_8256024 : Nat := 4983230072969 + 3 ^ 40 * 8256024 * 2
def baseEnd_8256024 : Nat := 4239308607055511501831243

theorem tailTrace_8256024 : CollatzResearch.WordTrace tailWord_8256024 prefixEnd_8256024 4239308607055511501831243 := by
  unfold tailWord_8256024
  simp only [CollatzResearch.WordTrace]
  refine ⟨150560966720921269743575563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200747955627895026324767417 150560966720921269743575563)
  ·
    refine ⟨225841450081381904615363345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150560966720921269743575563 225841450081381904615363345)
    ·
      refine ⟨169381087561036428461522509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225841450081381904615363345 169381087561036428461522509)
      ·
        refine ⟨63517907835388660673070941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169381087561036428461522509 63517907835388660673070941)
        ·
          refine ⟨23819215438270747752401603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63517907835388660673070941 23819215438270747752401603)
          ·
            refine ⟨35728823157406121628602405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819215438270747752401603 35728823157406121628602405)
            ·
              refine ⟨6699154342013647805362951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35728823157406121628602405 6699154342013647805362951)
              ·
                refine ⟨10048731513020471708044427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699154342013647805362951 10048731513020471708044427)
                ·
                  refine ⟨15073097269530707562066641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048731513020471708044427 15073097269530707562066641)
                  ·
                    refine ⟨11304822952148030671549981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15073097269530707562066641 11304822952148030671549981)
                    ·
                      refine ⟨4239308607055511501831243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304822952148030671549981 4239308607055511501831243)
                      ·
                        rfl

theorem cell23_8256024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_8256024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256024 prefixEnd_8256024 := by exact prefixLift 8256024
  have htrace : WordTrace (prefixWord ++ tailWord_8256024) baseStart_8256024 baseEnd_8256024 := by
    simpa [prefixWord, tailWord_8256024, baseEnd_8256024] using wordTrace_append hprefix tailTrace_8256024
  have hstable : (prefixWord ++ tailWord_8256024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256024).length < 2 ^ (prefixWord ++ tailWord_8256024).sum := by decide
  have hdescent : baseEnd_8256024 < baseStart_8256024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256043 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_8256043 : Nat := 118140960795 + 8256043 * 2 ^ 59
def prefixEnd_8256043 : Nat := 4983230072969 + 3 ^ 40 * 8256043 * 2
def baseEnd_8256043 : Nat := 4239318363187946927493655

theorem tailTrace_8256043 : CollatzResearch.WordTrace tailWord_8256043 prefixEnd_8256043 4239318363187946927493655 := by
  unfold tailWord_8256043
  simp only [CollatzResearch.WordTrace]
  refine ⟨301122626428773705732092783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200748417619182470488061855 301122626428773705732092783)
  ·
    refine ⟨451683939643160558598139175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301122626428773705732092783 451683939643160558598139175)
    ·
      refine ⟨677525909464740837897208763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451683939643160558598139175 677525909464740837897208763)
      ·
        refine ⟨1016288864197111256845813145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677525909464740837897208763 1016288864197111256845813145)
        ·
          refine ⟨762216648147833442634359859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016288864197111256845813145 762216648147833442634359859)
          ·
            refine ⟨1143324972221750163951539789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762216648147833442634359859 1143324972221750163951539789)
            ·
              refine ⟨428746864583156311481827421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143324972221750163951539789 428746864583156311481827421)
              ·
                refine ⟨160780074218683616805685283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428746864583156311481827421 160780074218683616805685283)
                ·
                  refine ⟨241170111328025425208527925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160780074218683616805685283 241170111328025425208527925)
                  ·
                    refine ⟨22609697937002383613299493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241170111328025425208527925 22609697937002383613299493)
                    ·
                      refine ⟨4239318363187946927493655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22609697937002383613299493 4239318363187946927493655)
                      ·
                        rfl

theorem cell23_8256043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_8256043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256043 prefixEnd_8256043 := by exact prefixLift 8256043
  have htrace : WordTrace (prefixWord ++ tailWord_8256043) baseStart_8256043 baseEnd_8256043 := by
    simpa [prefixWord, tailWord_8256043, baseEnd_8256043] using wordTrace_append hprefix tailTrace_8256043
  have hstable : (prefixWord ++ tailWord_8256043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256043).length < 2 ^ (prefixWord ++ tailWord_8256043).sum := by decide
  have hdescent : baseEnd_8256043 < baseStart_8256043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256054 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_8256054 : Nat := 118140960795 + 8256054 * 2 ^ 59
def prefixEnd_8256054 : Nat := 4983230072969 + 3 ^ 40 * 8256054 * 2
def baseEnd_8256054 : Nat := 4239324011475146384456105

theorem tailTrace_8256054 : CollatzResearch.WordTrace tailWord_8256054 prefixEnd_8256054 4239324011475146384456105 := by
  unfold tailWord_8256054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820189226983365913171451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200748685087822569740495477 18820189226983365913171451)
  ·
    refine ⟨28230283840475048869757177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18820189226983365913171451 28230283840475048869757177)
    ·
      refine ⟨21172712880356286652317883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28230283840475048869757177 21172712880356286652317883)
      ·
        refine ⟨31759069320534429978476825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21172712880356286652317883 31759069320534429978476825)
        ·
          refine ⟨23819301990400822483857619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31759069320534429978476825 23819301990400822483857619)
          ·
            refine ⟨35728952985601233725786429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819301990400822483857619 35728952985601233725786429)
            ·
              refine ⟨13398357369600462647169911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35728952985601233725786429 13398357369600462647169911)
              ·
                refine ⟨20097536054400693970754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13398357369600462647169911 20097536054400693970754867)
                ·
                  refine ⟨30146304081601040956132301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20097536054400693970754867 30146304081601040956132301)
                  ·
                    refine ⟨11304864030600390358549613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30146304081601040956132301 11304864030600390358549613)
                    ·
                      refine ⟨4239324011475146384456105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11304864030600390358549613 4239324011475146384456105)
                      ·
                        rfl

theorem cell23_8256054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_8256054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256054 prefixEnd_8256054 := by exact prefixLift 8256054
  have htrace : WordTrace (prefixWord ++ tailWord_8256054) baseStart_8256054 baseEnd_8256054 := by
    simpa [prefixWord, tailWord_8256054, baseEnd_8256054] using wordTrace_append hprefix tailTrace_8256054
  have hstable : (prefixWord ++ tailWord_8256054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256054).length < 2 ^ (prefixWord ++ tailWord_8256054).sum := by decide
  have hdescent : baseEnd_8256054 < baseStart_8256054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256111 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 2, 2, 2]
def baseStart_8256111 : Nat := 118140960795 + 8256111 * 2 ^ 59
def prefixEnd_8256111 : Nat := 4983230072969 + 3 ^ 40 * 8256111 * 2
def baseEnd_8256111 : Nat := 4239353279872452661443343

theorem tailTrace_8256111 : CollatzResearch.WordTrace tailWord_8256111 prefixEnd_8256111 4239353279872452661443343 := by
  unfold tailWord_8256111
  simp only [CollatzResearch.WordTrace]
  refine ⟨301125106592527353345568187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200750071061684902230378791 301125106592527353345568187)
  ·
    refine ⟨451687659888791030018352281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301125106592527353345568187 451687659888791030018352281)
    ·
      refine ⟨338765744916593272513764211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451687659888791030018352281 338765744916593272513764211)
      ·
        refine ⟨508148617374889908770646317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338765744916593272513764211 508148617374889908770646317)
        ·
          refine ⟨190555731515583715788992369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508148617374889908770646317 190555731515583715788992369)
          ·
            refine ⟨142916798636687786841744277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190555731515583715788992369 142916798636687786841744277)
            ·
              refine ⟨6699224936094740008206763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142916798636687786841744277 6699224936094740008206763)
              ·
                refine ⟨10048837404142110012310145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699224936094740008206763 10048837404142110012310145)
                ·
                  refine ⟨7536628053106582509232609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10048837404142110012310145 7536628053106582509232609)
                  ·
                    refine ⟨5652471039829936881924457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536628053106582509232609 5652471039829936881924457)
                    ·
                      refine ⟨4239353279872452661443343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652471039829936881924457 4239353279872452661443343)
                      ·
                        rfl

theorem cell23_8256111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 2, 2].length) (baseStart_8256111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256111 prefixEnd_8256111 := by exact prefixLift 8256111
  have htrace : WordTrace (prefixWord ++ tailWord_8256111) baseStart_8256111 baseEnd_8256111 := by
    simpa [prefixWord, tailWord_8256111, baseEnd_8256111] using wordTrace_append hprefix tailTrace_8256111
  have hstable : (prefixWord ++ tailWord_8256111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256111).length < 2 ^ (prefixWord ++ tailWord_8256111).sum := by decide
  have hdescent : baseEnd_8256111 < baseStart_8256111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256257 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_8256257 : Nat := 118140960795 + 8256257 * 2 ^ 59
def prefixEnd_8256257 : Nat := 4983230072969 + 3 ^ 40 * 8256257 * 2
def baseEnd_8256257 : Nat := 4239428248048009090217671

theorem tailTrace_8256257 : CollatzResearch.WordTrace tailWord_8256257 prefixEnd_8256257 4239428248048009090217671 := by
  unfold tailWord_8256257
  simp only [CollatzResearch.WordTrace]
  refine ⟨301130431649998420280383025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200753621099998946853588683 301130431649998420280383025)
  ·
    refine ⟨225847823737498815210287269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301130431649998420280383025 225847823737498815210287269)
    ·
      refine ⟨42346466950781027851928863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225847823737498815210287269 42346466950781027851928863)
      ·
        refine ⟨63519700426171541777893295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42346466950781027851928863 63519700426171541777893295)
        ·
          refine ⟨95279550639257312666839943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63519700426171541777893295 95279550639257312666839943)
          ·
            refine ⟨142919325958885969000259915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95279550639257312666839943 142919325958885969000259915)
            ·
              refine ⟨214378988938328953500389873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142919325958885969000259915 214378988938328953500389873)
              ·
                refine ⟨160784241703746715125292405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214378988938328953500389873 160784241703746715125292405)
                ·
                  refine ⟨15073522659726254542996163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160784241703746715125292405 15073522659726254542996163)
                  ·
                    refine ⟨22610283989589381814494245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15073522659726254542996163 22610283989589381814494245)
                    ·
                      refine ⟨4239428248048009090217671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22610283989589381814494245 4239428248048009090217671)
                      ·
                        rfl

theorem cell23_8256257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_8256257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256257 prefixEnd_8256257 := by exact prefixLift 8256257
  have htrace : WordTrace (prefixWord ++ tailWord_8256257) baseStart_8256257 baseEnd_8256257 := by
    simpa [prefixWord, tailWord_8256257, baseEnd_8256257] using wordTrace_append hprefix tailTrace_8256257
  have hstable : (prefixWord ++ tailWord_8256257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256257).length < 2 ^ (prefixWord ++ tailWord_8256257).sum := by decide
  have hdescent : baseEnd_8256257 < baseStart_8256257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256277 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_8256277 : Nat := 118140960795 + 8256277 * 2 ^ 59
def prefixEnd_8256277 : Nat := 4983230072969 + 3 ^ 40 * 8256277 * 2
def baseEnd_8256277 : Nat := 4239438517661099011967579

theorem tailTrace_8256277 : CollatzResearch.WordTrace tailWord_8256277 prefixEnd_8256277 4239438517661099011967579 := by
  unfold tailWord_8256277
  simp only [CollatzResearch.WordTrace]
  refine ⟨301131161109925963696111085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200754107406617309130740723 301131161109925963696111085)
  ·
    refine ⟨112924185416222236386041657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301131161109925963696111085 112924185416222236386041657)
    ·
      refine ⟨84693139062166677289531243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112924185416222236386041657 84693139062166677289531243)
      ·
        refine ⟨127039708593250015934296865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84693139062166677289531243 127039708593250015934296865)
        ·
          refine ⟨95279781444937511950722649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127039708593250015934296865 95279781444937511950722649)
          ·
            refine ⟨71459836083703133963041987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95279781444937511950722649 71459836083703133963041987)
            ·
              refine ⟨107189754125554700944562981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71459836083703133963041987 107189754125554700944562981)
              ·
                refine ⟨20098078898541506427105559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107189754125554700944562981 20098078898541506427105559)
                ·
                  refine ⟨30147118347812259640658339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20098078898541506427105559 30147118347812259640658339)
                  ·
                    refine ⟨45220677521718389460987509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30147118347812259640658339 45220677521718389460987509)
                    ·
                      refine ⟨4239438517661099011967579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45220677521718389460987509 4239438517661099011967579)
                      ·
                        rfl

theorem cell23_8256277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_8256277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256277 prefixEnd_8256277 := by exact prefixLift 8256277
  have htrace : WordTrace (prefixWord ++ tailWord_8256277) baseStart_8256277 baseEnd_8256277 := by
    simpa [prefixWord, tailWord_8256277, baseEnd_8256277] using wordTrace_append hprefix tailTrace_8256277
  have hstable : (prefixWord ++ tailWord_8256277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256277).length < 2 ^ (prefixWord ++ tailWord_8256277).sum := by decide
  have hdescent : baseEnd_8256277 < baseStart_8256277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256287 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_8256287 : Nat := 118140960795 + 8256287 * 2 ^ 59
def prefixEnd_8256287 : Nat := 4983230072969 + 3 ^ 40 * 8256287 * 2
def baseEnd_8256287 : Nat := 4239443652467643972842533

theorem tailTrace_8256287 : CollatzResearch.WordTrace tailWord_8256287 prefixEnd_8256287 4239443652467643972842533 := by
  unfold tailWord_8256287
  simp only [CollatzResearch.WordTrace]
  refine ⟨301131525839889735403975115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200754350559926490269316743 301131525839889735403975115)
  ·
    refine ⟨451697288759834603105962673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301131525839889735403975115 451697288759834603105962673)
    ·
      refine ⟨338772966569875952329472005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451697288759834603105962673 338772966569875952329472005)
      ·
        refine ⟨63519931231851741061776001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338772966569875952329472005 63519931231851741061776001)
        ·
          refine ⟨47639948423888805796332001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63519931231851741061776001 47639948423888805796332001)
          ·
            refine ⟨35729961317916604347249001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47639948423888805796332001 35729961317916604347249001)
            ·
              refine ⟨26797470988437453260436751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35729961317916604347249001 26797470988437453260436751)
              ·
                refine ⟨40196206482656179890655127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26797470988437453260436751 40196206482656179890655127)
                ·
                  refine ⟨60294309723984269835982691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40196206482656179890655127 60294309723984269835982691)
                  ·
                    refine ⟨90441464585976404753974037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60294309723984269835982691 90441464585976404753974037)
                    ·
                      refine ⟨4239443652467643972842533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90441464585976404753974037 4239443652467643972842533)
                      ·
                        rfl

theorem cell23_8256287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_8256287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256287 prefixEnd_8256287 := by exact prefixLift 8256287
  have htrace : WordTrace (prefixWord ++ tailWord_8256287) baseStart_8256287 baseEnd_8256287 := by
    simpa [prefixWord, tailWord_8256287, baseEnd_8256287] using wordTrace_append hprefix tailTrace_8256287
  have hstable : (prefixWord ++ tailWord_8256287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256287).length < 2 ^ (prefixWord ++ tailWord_8256287).sum := by decide
  have hdescent : baseEnd_8256287 < baseStart_8256287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256311 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_8256311 : Nat := 118140960795 + 8256311 * 2 ^ 59
def prefixEnd_8256311 : Nat := 4983230072969 + 3 ^ 40 * 8256311 * 2
def baseEnd_8256311 : Nat := 4239455976003351878942423

theorem tailTrace_8256311 : CollatzResearch.WordTrace tailWord_8256311 prefixEnd_8256311 4239455976003351878942423 := by
  unfold tailWord_8256311
  simp only [CollatzResearch.WordTrace]
  refine ⟨301132401191802787502848787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200754934127868525001899191 301132401191802787502848787)
  ·
    refine ⟨451698601787704181254273181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301132401191802787502848787 451698601787704181254273181)
    ·
      refine ⟨169386975670389067970352443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451698601787704181254273181 169386975670389067970352443)
      ·
        refine ⟨254080463505583601955528665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169386975670389067970352443 254080463505583601955528665)
        ·
          refine ⟨190560347629187701466646499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254080463505583601955528665 190560347629187701466646499)
          ·
            refine ⟨285840521443781552199969749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190560347629187701466646499 285840521443781552199969749)
            ·
              refine ⟨6699387221338630129686791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285840521443781552199969749 6699387221338630129686791)
              ·
                refine ⟨10049080832007945194530187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699387221338630129686791 10049080832007945194530187)
                ·
                  refine ⟨15073621248011917791795281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049080832007945194530187 15073621248011917791795281)
                  ·
                    refine ⟨11305215936008938343846461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15073621248011917791795281 11305215936008938343846461)
                    ·
                      refine ⟨4239455976003351878942423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11305215936008938343846461 4239455976003351878942423)
                      ·
                        rfl

theorem cell23_8256311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_8256311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256311 prefixEnd_8256311 := by exact prefixLift 8256311
  have htrace : WordTrace (prefixWord ++ tailWord_8256311) baseStart_8256311 baseEnd_8256311 := by
    simpa [prefixWord, tailWord_8256311, baseEnd_8256311] using wordTrace_append hprefix tailTrace_8256311
  have hstable : (prefixWord ++ tailWord_8256311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256311).length < 2 ^ (prefixWord ++ tailWord_8256311).sum := by decide
  have hdescent : baseEnd_8256311 < baseStart_8256311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256318 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_8256318 : Nat := 118140960795 + 8256318 * 2 ^ 59
def prefixEnd_8256318 : Nat := 4983230072969 + 3 ^ 40 * 8256318 * 2
def baseEnd_8256318 : Nat := 1413153190122644450518297

theorem tailTrace_8256318 : CollatzResearch.WordTrace tailWord_8256318 prefixEnd_8256318 1413153190122644450518297 := by
  unfold tailWord_8256318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641582062847178462294201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200755104335184951798902405 37641582062847178462294201)
  ·
    refine ⟨28231186547135383846720651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37641582062847178462294201 28231186547135383846720651)
    ·
      refine ⟨42346779820703075770080977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28231186547135383846720651 42346779820703075770080977)
      ·
        refine ⟨31760084865527306827560733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42346779820703075770080977 31760084865527306827560733)
        ·
          refine ⟨11910031824572740060335275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31760084865527306827560733 11910031824572740060335275)
          ·
            refine ⟨17865047736859110090502913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910031824572740060335275 17865047736859110090502913)
            ·
              refine ⟨13398785802644332567877185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17865047736859110090502913 13398785802644332567877185)
              ·
                refine ⟨10049089351983249425907889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13398785802644332567877185 10049089351983249425907889)
                ·
                  refine ⟨7536817013987437069430917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10049089351983249425907889 7536817013987437069430917)
                  ·
                    refine ⟨1413153190122644450518297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536817013987437069430917 1413153190122644450518297)
                    ·
                      rfl

theorem cell23_8256318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_8256318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256318 prefixEnd_8256318 := by exact prefixLift 8256318
  have htrace : WordTrace (prefixWord ++ tailWord_8256318) baseStart_8256318 baseEnd_8256318 := by
    simpa [prefixWord, tailWord_8256318, baseEnd_8256318] using wordTrace_append hprefix tailTrace_8256318
  have hstable : (prefixWord ++ tailWord_8256318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256318).length < 2 ^ (prefixWord ++ tailWord_8256318).sum := by decide
  have hdescent : baseEnd_8256318 < baseStart_8256318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256341 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_8256341 : Nat := 118140960795 + 8256341 * 2 ^ 59
def prefixEnd_8256341 : Nat := 4983230072969 + 3 ^ 40 * 8256341 * 2
def baseEnd_8256341 : Nat := 4239471380422986761567285

theorem tailTrace_8256341 : CollatzResearch.WordTrace tailWord_8256341 prefixEnd_8256341 4239471380422986761567285 := by
  unfold tailWord_8256341
  simp only [CollatzResearch.WordTrace]
  refine ⟨301133495381694102626440877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200755663587796068417627251 301133495381694102626440877)
  ·
    refine ⟨112925060768135288484915329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301133495381694102626440877 112925060768135288484915329)
    ·
      refine ⟨84693795576101466363686497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112925060768135288484915329 84693795576101466363686497)
      ·
        refine ⟨63520346682076099772764873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84693795576101466363686497 63520346682076099772764873)
        ·
          refine ⟨47640260011557074829573655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63520346682076099772764873 47640260011557074829573655)
          ·
            refine ⟨71460390017335612244360483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47640260011557074829573655 71460390017335612244360483)
            ·
              refine ⟨107190585026003418366540725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71460390017335612244360483 107190585026003418366540725)
              ·
                refine ⟨10049117346187820471863193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107190585026003418366540725 10049117346187820471863193)
                ·
                  refine ⟨7536838009640865353897395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10049117346187820471863193 7536838009640865353897395)
                  ·
                    refine ⟨11305257014461298030846093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7536838009640865353897395 11305257014461298030846093)
                    ·
                      refine ⟨4239471380422986761567285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11305257014461298030846093 4239471380422986761567285)
                      ·
                        rfl

theorem cell23_8256341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_8256341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256341 prefixEnd_8256341 := by exact prefixLift 8256341
  have htrace : WordTrace (prefixWord ++ tailWord_8256341) baseStart_8256341 baseEnd_8256341 := by
    simpa [prefixWord, tailWord_8256341, baseEnd_8256341] using wordTrace_append hprefix tailTrace_8256341
  have hstable : (prefixWord ++ tailWord_8256341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256341).length < 2 ^ (prefixWord ++ tailWord_8256341).sum := by decide
  have hdescent : baseEnd_8256341 < baseStart_8256341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256351 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 1, 3, 2]
def baseStart_8256351 : Nat := 118140960795 + 8256351 * 2 ^ 59
def prefixEnd_8256351 : Nat := 4983230072969 + 3 ^ 40 * 8256351 * 2
def baseEnd_8256351 : Nat := 4239476515229531722442239

theorem tailTrace_8256351 : CollatzResearch.WordTrace tailWord_8256351 prefixEnd_8256351 4239476515229531722442239 := by
  unfold tailWord_8256351
  simp only [CollatzResearch.WordTrace]
  refine ⟨301133860111657874334304907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200755906741105249556203271 301133860111657874334304907)
  ·
    refine ⟨451700790167486811501457361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301133860111657874334304907 451700790167486811501457361)
    ·
      refine ⟨338775592625615108626093021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451700790167486811501457361 338775592625615108626093021)
      ·
        refine ⟨127040847234605665734784883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338775592625615108626093021 127040847234605665734784883)
        ·
          refine ⟨190561270851908498602177325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127040847234605665734784883 190561270851908498602177325)
          ·
            refine ⟨71460476569465686975816497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190561270851908498602177325 71460476569465686975816497)
            ·
              refine ⟨53595357427099265231862373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71460476569465686975816497 53595357427099265231862373)
              ·
                refine ⟨10049129517581112230974195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53595357427099265231862373 10049129517581112230974195)
                ·
                  refine ⟨15073694276371668346461293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049129517581112230974195 15073694276371668346461293)
                  ·
                    refine ⟨5652635353639375629922985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15073694276371668346461293 5652635353639375629922985)
                    ·
                      refine ⟨4239476515229531722442239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652635353639375629922985 4239476515229531722442239)
                      ·
                        rfl

theorem cell23_8256351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_8256351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256351 prefixEnd_8256351 := by exact prefixLift 8256351
  have htrace : WordTrace (prefixWord ++ tailWord_8256351) baseStart_8256351 baseEnd_8256351 := by
    simpa [prefixWord, tailWord_8256351, baseEnd_8256351] using wordTrace_append hprefix tailTrace_8256351
  have hstable : (prefixWord ++ tailWord_8256351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256351).length < 2 ^ (prefixWord ++ tailWord_8256351).sum := by decide
  have hdescent : baseEnd_8256351 < baseStart_8256351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256367 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_8256367 : Nat := 118140960795 + 8256367 * 2 ^ 59
def prefixEnd_8256367 : Nat := 4983230072969 + 3 ^ 40 * 8256367 * 2
def baseEnd_8256367 : Nat := 4239484730920003659842165

theorem tailTrace_8256367 : CollatzResearch.WordTrace tailWord_8256367 prefixEnd_8256367 4239484730920003659842165 := by
  unfold tailWord_8256367
  simp only [CollatzResearch.WordTrace]
  refine ⟨301134443679599909066887355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200756295786399939377924903 301134443679599909066887355)
  ·
    refine ⟨451701665519399863600331033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301134443679599909066887355 451701665519399863600331033)
    ·
      refine ⟨338776249139549897700248275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451701665519399863600331033 338776249139549897700248275)
      ·
        refine ⟨508164373709324846550372413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338776249139549897700248275 508164373709324846550372413)
        ·
          refine ⟨190561640140996817456389655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508164373709324846550372413 190561640140996817456389655)
          ·
            refine ⟨285842460211495226184584483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190561640140996817456389655 285842460211495226184584483)
            ·
              refine ⟨428763690317242839276876725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285842460211495226184584483 428763690317242839276876725)
              ·
                refine ⟨40196595967241516182207193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428763690317242839276876725 40196595967241516182207193)
                ·
                  refine ⟨30147446975431137136655395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40196595967241516182207193 30147446975431137136655395)
                  ·
                    refine ⟨45221170463146705704983093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30147446975431137136655395 45221170463146705704983093)
                    ·
                      refine ⟨4239484730920003659842165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45221170463146705704983093 4239484730920003659842165)
                      ·
                        rfl

theorem cell23_8256367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_8256367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256367 prefixEnd_8256367 := by exact prefixLift 8256367
  have htrace : WordTrace (prefixWord ++ tailWord_8256367) baseStart_8256367 baseEnd_8256367 := by
    simpa [prefixWord, tailWord_8256367, baseEnd_8256367] using wordTrace_append hprefix tailTrace_8256367
  have hstable : (prefixWord ++ tailWord_8256367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256367).length < 2 ^ (prefixWord ++ tailWord_8256367).sum := by decide
  have hdescent : baseEnd_8256367 < baseStart_8256367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256368 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2]
def baseStart_8256368 : Nat := 118140960795 + 8256368 * 2 ^ 59
def prefixEnd_8256368 : Nat := 4983230072969 + 3 ^ 40 * 8256368 * 2
def baseEnd_8256368 : Nat := 4239485244400658155929661

theorem tailTrace_8256368 : CollatzResearch.WordTrace tailWord_8256368 prefixEnd_8256368 4239485244400658155929661 := by
  unfold tailWord_8256368
  simp only [CollatzResearch.WordTrace]
  refine ⟨150567240076298143118836879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200756320101730857491782505 150567240076298143118836879)
  ·
    refine ⟨225850860114447214678255319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150567240076298143118836879 225850860114447214678255319)
    ·
      refine ⟨338776290171670822017382979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225850860114447214678255319 338776290171670822017382979)
      ·
        refine ⟨508164435257506233026074469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338776290171670822017382979 508164435257506233026074469)
        ·
          refine ⟨95280831610782418692388963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508164435257506233026074469 95280831610782418692388963)
          ·
            refine ⟨142921247416173628038583445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95280831610782418692388963 142921247416173628038583445)
            ·
              refine ⟨6699433472633138814308599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142921247416173628038583445 6699433472633138814308599)
              ·
                refine ⟨10049150208949708221462899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699433472633138814308599 10049150208949708221462899)
                ·
                  refine ⟨15073725313424562332194349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049150208949708221462899 15073725313424562332194349)
                  ·
                    refine ⟨5652646992534210874572881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15073725313424562332194349 5652646992534210874572881)
                    ·
                      refine ⟨4239485244400658155929661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652646992534210874572881 4239485244400658155929661)
                      ·
                        rfl

theorem cell23_8256368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2].length) (baseStart_8256368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256368 prefixEnd_8256368 := by exact prefixLift 8256368
  have htrace : WordTrace (prefixWord ++ tailWord_8256368) baseStart_8256368 baseEnd_8256368 := by
    simpa [prefixWord, tailWord_8256368, baseEnd_8256368] using wordTrace_append hprefix tailTrace_8256368
  have hstable : (prefixWord ++ tailWord_8256368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256368).length < 2 ^ (prefixWord ++ tailWord_8256368).sum := by decide
  have hdescent : baseEnd_8256368 < baseStart_8256368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256404 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 7]
def baseStart_8256404 : Nat := 118140960795 + 8256404 * 2 ^ 59
def prefixEnd_8256404 : Nat := 4983230072969 + 3 ^ 40 * 8256404 * 2
def baseEnd_8256404 : Nat := 471055969967135557231055

theorem tailTrace_8256404 : CollatzResearch.WordTrace tailWord_8256404 prefixEnd_8256404 471055969967135557231055 := by
  unfold tailWord_8256404
  simp only [CollatzResearch.WordTrace]
  refine ⟨150567896590232932192992133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200757195453643909590656177 150567896590232932192992133)
  ·
    refine ⟨28231480610668674786186025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150567896590232932192992133 28231480610668674786186025)
    ·
      refine ⟨21173610458001506089639519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28231480610668674786186025 21173610458001506089639519)
      ·
        refine ⟨31760415687002259134459279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21173610458001506089639519 31760415687002259134459279)
        ·
          refine ⟨47640623530503388701688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31760415687002259134459279 47640623530503388701688919)
          ·
            refine ⟨71460935295755083052533379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47640623530503388701688919 71460935295755083052533379)
            ·
              refine ⟨107191402943632624578800069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71460935295755083052533379 107191402943632624578800069)
              ·
                refine ⟨20098388051931117108525013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107191402943632624578800069 20098388051931117108525013)
                ·
                  refine ⟨471055969967135557231055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20098388051931117108525013 471055969967135557231055)
                  ·
                    rfl

theorem cell23_8256404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_8256404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256404 prefixEnd_8256404 := by exact prefixLift 8256404
  have htrace : WordTrace (prefixWord ++ tailWord_8256404) baseStart_8256404 baseEnd_8256404 := by
    simpa [prefixWord, tailWord_8256404, baseEnd_8256404] using wordTrace_append hprefix tailTrace_8256404
  have hstable : (prefixWord ++ tailWord_8256404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256404).length < 2 ^ (prefixWord ++ tailWord_8256404).sum := by decide
  have hdescent : baseEnd_8256404 < baseStart_8256404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_8256427 : Nat := 118140960795 + 8256427 * 2 ^ 59
def prefixEnd_8256427 : Nat := 4983230072969 + 3 ^ 40 * 8256427 * 2
def baseEnd_8256427 : Nat := 4239515539759273425091889

theorem tailTrace_8256427 : CollatzResearch.WordTrace tailWord_8256427 prefixEnd_8256427 4239515539759273425091889 := by
  unfold tailWord_8256427
  simp only [CollatzResearch.WordTrace]
  refine ⟨301136632059382539314071535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200757754706255026209381023 301136632059382539314071535)
  ·
    refine ⟨451704948089073808971107303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301136632059382539314071535 451704948089073808971107303)
    ·
      refine ⟨677557422133610713456660955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451704948089073808971107303 677557422133610713456660955)
      ·
        refine ⟨1016336133200416070184991433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677557422133610713456660955 1016336133200416070184991433)
        ·
          refine ⟨762252099900312052638743575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016336133200416070184991433 762252099900312052638743575)
          ·
            refine ⟨1143378149850468078958115363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762252099900312052638743575 1143378149850468078958115363)
            ·
              refine ⟨1715067224775702118437173045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143378149850468078958115363 1715067224775702118437173045)
              ·
                refine ⟨160787552322722073603484973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1715067224775702118437173045 160787552322722073603484973)
                ·
                  refine ⟨60295332121020777601306865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160787552322722073603484973 60295332121020777601306865)
                  ·
                    refine ⟨45221499090765583200980149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60295332121020777601306865 45221499090765583200980149)
                    ·
                      refine ⟨4239515539759273425091889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45221499090765583200980149 4239515539759273425091889)
                      ·
                        rfl

theorem cell23_8256427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_8256427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256427 prefixEnd_8256427 := by exact prefixLift 8256427
  have htrace : WordTrace (prefixWord ++ tailWord_8256427) baseStart_8256427 baseEnd_8256427 := by
    simpa [prefixWord, tailWord_8256427, baseEnd_8256427] using wordTrace_append hprefix tailTrace_8256427
  have hstable : (prefixWord ++ tailWord_8256427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256427).length < 2 ^ (prefixWord ++ tailWord_8256427).sum := by decide
  have hdescent : baseEnd_8256427 < baseStart_8256427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256447 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 8]
def baseStart_8256447 : Nat := 118140960795 + 8256447 * 2 ^ 59
def prefixEnd_8256447 : Nat := 4983230072969 + 3 ^ 40 * 8256447 * 2
def baseEnd_8256447 : Nat := 1413175269790787782280599

theorem tailTrace_8256447 : CollatzResearch.WordTrace tailWord_8256447 prefixEnd_8256447 1413175269790787782280599 := by
  unfold tailWord_8256447
  simp only [CollatzResearch.WordTrace]
  refine ⟨301137361519310082729799595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200758241012873388486533063 301137361519310082729799595)
  ·
    refine ⟨451706042278965124094699393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301137361519310082729799595 451706042278965124094699393)
    ·
      refine ⟨338779531709223843071024545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451706042278965124094699393 338779531709223843071024545)
      ·
        refine ⟨254084648781917882303268409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338779531709223843071024545 254084648781917882303268409)
        ·
          refine ⟨190563486586438411727451307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254084648781917882303268409 190563486586438411727451307)
          ·
            refine ⟨285845229879657617591176961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190563486586438411727451307 285845229879657617591176961)
            ·
              refine ⟨214383922409743213193382721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285845229879657617591176961 214383922409743213193382721)
              ·
                refine ⟨160787941807307409895037041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214383922409743213193382721 160787941807307409895037041)
                ·
                  refine ⟨120590956355480557421277781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160787941807307409895037041 120590956355480557421277781)
                  ·
                    refine ⟨1413175269790787782280599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120590956355480557421277781 1413175269790787782280599)
                    ·
                      rfl

theorem cell23_8256447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_8256447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256447 prefixEnd_8256447 := by exact prefixLift 8256447
  have htrace : WordTrace (prefixWord ++ tailWord_8256447) baseStart_8256447 baseEnd_8256447 := by
    simpa [prefixWord, tailWord_8256447, baseEnd_8256447] using wordTrace_append hprefix tailTrace_8256447
  have hstable : (prefixWord ++ tailWord_8256447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256447).length < 2 ^ (prefixWord ++ tailWord_8256447).sum := by decide
  have hdescent : baseEnd_8256447 < baseStart_8256447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256464 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_8256464 : Nat := 118140960795 + 8256464 * 2 ^ 59
def prefixEnd_8256464 : Nat := 4983230072969 + 3 ^ 40 * 8256464 * 2
def baseEnd_8256464 : Nat := 1413178179514496593443073

theorem tailTrace_8256464 : CollatzResearch.WordTrace tailWord_8256464 prefixEnd_8256464 1413178179514496593443073 := by
  unfold tailWord_8256464
  simp only [CollatzResearch.WordTrace]
  refine ⟨150568990780124247316584223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200758654373498996422112297 150568990780124247316584223)
  ·
    refine ⟨225853486170186370974876335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150568990780124247316584223 225853486170186370974876335)
    ·
      refine ⟨338780229255279556462314503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225853486170186370974876335 338780229255279556462314503)
      ·
        refine ⟨508170343882919334693471755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338780229255279556462314503 508170343882919334693471755)
        ·
          refine ⟨762255515824379002040207633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508170343882919334693471755 762255515824379002040207633)
          ·
            refine ⟨571691636868284251530155725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762255515824379002040207633 571691636868284251530155725)
            ·
              refine ⟨214384363825606594323808397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571691636868284251530155725 214384363825606594323808397)
              ·
                refine ⟨80394136434602472871428149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214384363825606594323808397 80394136434602472871428149)
                ·
                  refine ⟨7536950290743981831696389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80394136434602472871428149 7536950290743981831696389)
                  ·
                    refine ⟨1413178179514496593443073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536950290743981831696389 1413178179514496593443073)
                    ·
                      rfl

theorem cell23_8256464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_8256464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256464 prefixEnd_8256464 := by exact prefixLift 8256464
  have htrace : WordTrace (prefixWord ++ tailWord_8256464) baseStart_8256464 baseEnd_8256464 := by
    simpa [prefixWord, tailWord_8256464, baseEnd_8256464] using wordTrace_append hprefix tailTrace_8256464
  have hstable : (prefixWord ++ tailWord_8256464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256464).length < 2 ^ (prefixWord ++ tailWord_8256464).sum := by decide
  have hdescent : baseEnd_8256464 < baseStart_8256464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256504 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_8256504 : Nat := 118140960795 + 8256504 * 2 ^ 59
def prefixEnd_8256504 : Nat := 4983230072969 + 3 ^ 40 * 8256504 * 2
def baseEnd_8256504 : Nat := 4239555077769669623829035

theorem tailTrace_8256504 : CollatzResearch.WordTrace tailWord_8256504 prefixEnd_8256504 4239555077769669623829035 := by
  unfold tailWord_8256504
  simp only [CollatzResearch.WordTrace]
  refine ⟨150569720240051790732312283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200759626986735720976416377 150569720240051790732312283)
  ·
    refine ⟨225854580360077686098468425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150569720240051790732312283 225854580360077686098468425)
    ·
      refine ⟨169390935270058264573851319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225854580360077686098468425 169390935270058264573851319)
      ·
        refine ⟨254086402905087396860776979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169390935270058264573851319 254086402905087396860776979)
        ·
          refine ⟨381129604357631095291165469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254086402905087396860776979 381129604357631095291165469)
          ·
            refine ⟨142923601634111660734187051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381129604357631095291165469 142923601634111660734187051)
            ·
              refine ⟨214385402451167491101280577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142923601634111660734187051 214385402451167491101280577)
              ·
                refine ⟨160789051838375618325960433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214385402451167491101280577 160789051838375618325960433)
                ·
                  refine ⟨120591788878781713744470325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160789051838375618325960433 120591788878781713744470325)
                  ·
                    refine ⟨11305480207385785663544093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120591788878781713744470325 11305480207385785663544093)
                    ·
                      refine ⟨4239555077769669623829035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11305480207385785663544093 4239555077769669623829035)
                      ·
                        rfl

theorem cell23_8256504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_8256504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256504 prefixEnd_8256504 := by exact prefixLift 8256504
  have htrace : WordTrace (prefixWord ++ tailWord_8256504) baseStart_8256504 baseEnd_8256504 := by
    simpa [prefixWord, tailWord_8256504, baseEnd_8256504] using wordTrace_append hprefix tailTrace_8256504
  have hstable : (prefixWord ++ tailWord_8256504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256504).length < 2 ^ (prefixWord ++ tailWord_8256504).sum := by decide
  have hdescent : baseEnd_8256504 < baseStart_8256504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
