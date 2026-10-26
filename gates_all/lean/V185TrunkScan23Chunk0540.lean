import V185TrunkScan23Chunk0539

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3192691 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_3192691 : Nat := 118140960795 + 3192691 * 2 ^ 59
def prefixEnd_3192691 : Nat := 4983230072969 + 3 ^ 40 * 3192691 * 2
def baseEnd_3192691 : Nat := 1639385064283873315479587

theorem tailTrace_3192691 : CollatzResearch.WordTrace tailWord_3192691 prefixEnd_3192691 1639385064283873315479587 := by
  unfold tailWord_3192691
  simp only [CollatzResearch.WordTrace]
  refine ⟨116447007276433250056889927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77631338184288833371259951 116447007276433250056889927)
  ·
    refine ⟨174670510914649875085334891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116447007276433250056889927 174670510914649875085334891)
    ·
      refine ⟨262005766371974812628002337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174670510914649875085334891 262005766371974812628002337)
      ·
        refine ⟨196504324778981109471001753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262005766371974812628002337 196504324778981109471001753)
        ·
          refine ⟨147378243584235832103251315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196504324778981109471001753 147378243584235832103251315)
          ·
            refine ⟨221067365376353748154876973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147378243584235832103251315 221067365376353748154876973)
            ·
              refine ⟨82900262016132655558078865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221067365376353748154876973 82900262016132655558078865)
              ·
                refine ⟨62175196512099491668559149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82900262016132655558078865 62175196512099491668559149)
                ·
                  refine ⟨23315698692037309375709681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62175196512099491668559149 23315698692037309375709681)
                  ·
                    refine ⟨17486774019027982031782261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23315698692037309375709681 17486774019027982031782261)
                    ·
                      refine ⟨1639385064283873315479587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17486774019027982031782261 1639385064283873315479587)
                      ·
                        rfl

theorem cell23_3192691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_3192691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192691 prefixEnd_3192691 := by exact prefixLift 3192691
  have htrace : WordTrace (prefixWord ++ tailWord_3192691) baseStart_3192691 baseEnd_3192691 := by
    simpa [prefixWord, tailWord_3192691, baseEnd_3192691] using wordTrace_append hprefix tailTrace_3192691
  have hstable : (prefixWord ++ tailWord_3192691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192691).length < 2 ^ (prefixWord ++ tailWord_3192691).sum := by decide
  have hdescent : baseEnd_3192691 < baseStart_3192691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192755 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3]
def baseStart_3192755 : Nat := 118140960795 + 3192755 * 2 ^ 59
def prefixEnd_3192755 : Nat := 4983230072969 + 3 ^ 40 * 3192755 * 2
def baseEnd_3192755 : Nat := 1639417927045761065079293

theorem tailTrace_3192755 : CollatzResearch.WordTrace tailWord_3192755 prefixEnd_3192755 1639417927045761065079293 := by
  unfold tailWord_3192755
  simp only [CollatzResearch.WordTrace]
  refine ⟨116449341548201388987219719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77632894365467592658146479 116449341548201388987219719)
  ·
    refine ⟨174674012322302083480829579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116449341548201388987219719 174674012322302083480829579)
    ·
      refine ⟨262011018483453125221244369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174674012322302083480829579 262011018483453125221244369)
      ·
        refine ⟨196508263862589843915933277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262011018483453125221244369 196508263862589843915933277)
        ·
          refine ⟨73690598948471191468474979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196508263862589843915933277 73690598948471191468474979)
          ·
            refine ⟨110535898422706787202712469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73690598948471191468474979 110535898422706787202712469)
            ·
              refine ⟨5181370238564380650127147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110535898422706787202712469 5181370238564380650127147)
              ·
                refine ⟨7772055357846570975190721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181370238564380650127147 7772055357846570975190721)
                ·
                  refine ⟨5829041518384928231393041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772055357846570975190721 5829041518384928231393041)
                  ·
                    refine ⟨4371781138788696173544781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829041518384928231393041 4371781138788696173544781)
                    ·
                      refine ⟨1639417927045761065079293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371781138788696173544781 1639417927045761065079293)
                      ·
                        rfl

theorem cell23_3192755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_3192755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192755 prefixEnd_3192755 := by exact prefixLift 3192755
  have htrace : WordTrace (prefixWord ++ tailWord_3192755) baseStart_3192755 baseEnd_3192755 := by
    simpa [prefixWord, tailWord_3192755, baseEnd_3192755] using wordTrace_append hprefix tailTrace_3192755
  have hstable : (prefixWord ++ tailWord_3192755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192755).length < 2 ^ (prefixWord ++ tailWord_3192755).sum := by decide
  have hdescent : baseEnd_3192755 < baseStart_3192755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192796 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3192796 : Nat := 118140960795 + 3192796 * 2 ^ 59
def prefixEnd_3192796 : Nat := 4983230072969 + 3 ^ 40 * 3192796 * 2
def baseEnd_3192796 : Nat := 546479659917531801555535

theorem tailTrace_3192796 : CollatzResearch.WordTrace tailWord_3192796 prefixEnd_3192796 546479659917531801555535 := by
  unfold tailWord_3192796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58225418470526426494731121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77633891294035235326308161 58225418470526426494731121)
  ·
    refine ⟨43669063852894819871048341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58225418470526426494731121 43669063852894819871048341)
    ·
      refine ⟨2046987368104444681455391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43669063852894819871048341 2046987368104444681455391)
      ·
        refine ⟨3070481052156667022183087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046987368104444681455391 3070481052156667022183087)
        ·
          refine ⟨4605721578235000533274631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070481052156667022183087 4605721578235000533274631)
          ·
            refine ⟨6908582367352500799911947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605721578235000533274631 6908582367352500799911947)
            ·
              refine ⟨10362873551028751199867921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908582367352500799911947 10362873551028751199867921)
              ·
                refine ⟨7772155163271563399900941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10362873551028751199867921 7772155163271563399900941)
                ·
                  refine ⟨2914558186226836274962853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7772155163271563399900941 2914558186226836274962853)
                  ·
                    refine ⟨546479659917531801555535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914558186226836274962853 546479659917531801555535)
                    ·
                      rfl

theorem cell23_3192796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3192796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192796 prefixEnd_3192796 := by exact prefixLift 3192796
  have htrace : WordTrace (prefixWord ++ tailWord_3192796) baseStart_3192796 baseEnd_3192796 := by
    simpa [prefixWord, tailWord_3192796, baseEnd_3192796] using wordTrace_append hprefix tailTrace_3192796
  have hstable : (prefixWord ++ tailWord_3192796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192796).length < 2 ^ (prefixWord ++ tailWord_3192796).sum := by decide
  have hdescent : baseEnd_3192796 < baseStart_3192796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192836 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3192836 : Nat := 118140960795 + 3192836 * 2 ^ 59
def prefixEnd_3192836 : Nat := 4983230072969 + 3 ^ 40 * 3192836 * 2
def baseEnd_3192836 : Nat := 1639459518978775248166421

theorem tailTrace_3192836 : CollatzResearch.WordTrace tailWord_3192836 prefixEnd_3192836 1639459518978775248166421 := by
  unfold tailWord_3192836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58226147930453969910459181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77634863907271959880612241 58226147930453969910459181)
  ·
    refine ⟨21834805473920238716422193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58226147930453969910459181 21834805473920238716422193)
    ·
      refine ⟨16376104105440179037316645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21834805473920238716422193 16376104105440179037316645)
      ·
        refine ⟨3070519519770033569496871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16376104105440179037316645 3070519519770033569496871)
        ·
          refine ⟨4605779279655050354245307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070519519770033569496871 4605779279655050354245307)
          ·
            refine ⟨6908668919482575531367961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605779279655050354245307 6908668919482575531367961)
            ·
              refine ⟨5181501689611931648525971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908668919482575531367961 5181501689611931648525971)
              ·
                refine ⟨7772252534417897472788957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181501689611931648525971 7772252534417897472788957)
                ·
                  refine ⟨2914594700406711552295859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7772252534417897472788957 2914594700406711552295859)
                  ·
                    refine ⟨4371892050610067328443789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914594700406711552295859 4371892050610067328443789)
                    ·
                      refine ⟨1639459518978775248166421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371892050610067328443789 1639459518978775248166421)
                      ·
                        rfl

theorem cell23_3192836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3192836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192836 prefixEnd_3192836 := by exact prefixLift 3192836
  have htrace : WordTrace (prefixWord ++ tailWord_3192836) baseStart_3192836 baseEnd_3192836 := by
    simpa [prefixWord, tailWord_3192836, baseEnd_3192836] using wordTrace_append hprefix tailTrace_3192836
  have hstable : (prefixWord ++ tailWord_3192836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192836).length < 2 ^ (prefixWord ++ tailWord_3192836).sum := by decide
  have hdescent : baseEnd_3192836 < baseStart_3192836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192865 : List Nat := [1, 2, 3, 2, 4, 1, 1, 9]
def baseStart_3192865 : Nat := 118140960795 + 3192865 * 2 ^ 59
def prefixEnd_3192865 : Nat := 4983230072969 + 3 ^ 40 * 3192865 * 2
def baseEnd_3192865 : Nat := 60721274441398356840881

theorem tailTrace_3192865 : CollatzResearch.WordTrace tailWord_3192865 prefixEnd_3192865 60721274441398356840881 := by
  unfold tailWord_3192865
  simp only [CollatzResearch.WordTrace]
  refine ⟨116453353577802877773724049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77635569051868585182482699 116453353577802877773724049)
  ·
    refine ⟨87340015183352158330293037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116453353577802877773724049 87340015183352158330293037)
    ·
      refine ⟨32752505693757059373859889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87340015183352158330293037 32752505693757059373859889)
      ·
        refine ⟨24564379270317794530394917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32752505693757059373859889 24564379270317794530394917)
        ·
          refine ⟨4605821113184586474449047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24564379270317794530394917 4605821113184586474449047)
          ·
            refine ⟨6908731669776879711673571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605821113184586474449047 6908731669776879711673571)
            ·
              refine ⟨10363097504665319567510357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908731669776879711673571 10363097504665319567510357)
              ·
                refine ⟨60721274441398356840881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10363097504665319567510357 60721274441398356840881)
                ·
                  rfl

theorem cell23_3192865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 9].length) (baseStart_3192865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192865 prefixEnd_3192865 := by exact prefixLift 3192865
  have htrace : WordTrace (prefixWord ++ tailWord_3192865) baseStart_3192865 baseEnd_3192865 := by
    simpa [prefixWord, tailWord_3192865, baseEnd_3192865] using wordTrace_append hprefix tailTrace_3192865
  have hstable : (prefixWord ++ tailWord_3192865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192865).length < 2 ^ (prefixWord ++ tailWord_3192865).sum := by decide
  have hdescent : baseEnd_3192865 < baseStart_3192865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192892 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_3192892 : Nat := 118140960795 + 3192892 * 2 ^ 59
def prefixEnd_3192892 : Nat := 4983230072969 + 3 ^ 40 * 3192892 * 2
def baseEnd_3192892 : Nat := 1639488273895427029066163

theorem tailTrace_3192892 : CollatzResearch.WordTrace tailWord_3192892 prefixEnd_3192892 1639488273895427029066163 := by
  unfold tailWord_3192892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227169174352530692478465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77636225565803374256637953 58227169174352530692478465)
  ·
    refine ⟨43670376880764398019358849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58227169174352530692478465 43670376880764398019358849)
    ·
      refine ⟨32752782660573298514519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43670376880764398019358849 32752782660573298514519137)
      ·
        refine ⟨24564586995429973885889353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32752782660573298514519137 24564586995429973885889353)
        ·
          refine ⟨18423440246572480414417015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564586995429973885889353 18423440246572480414417015)
          ·
            refine ⟨27635160369858720621625523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423440246572480414417015 27635160369858720621625523)
            ·
              refine ⟨41452740554788080932438285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27635160369858720621625523 41452740554788080932438285)
              ·
                refine ⟨15544777708045530349664357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41452740554788080932438285 15544777708045530349664357)
                ·
                  refine ⟨2914645820258536940562067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15544777708045530349664357 2914645820258536940562067)
                  ·
                    refine ⟨4371968730387805410843101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914645820258536940562067 4371968730387805410843101)
                    ·
                      refine ⟨1639488273895427029066163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371968730387805410843101 1639488273895427029066163)
                      ·
                        rfl

theorem cell23_3192892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_3192892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192892 prefixEnd_3192892 := by exact prefixLift 3192892
  have htrace : WordTrace (prefixWord ++ tailWord_3192892) baseStart_3192892 baseEnd_3192892 := by
    simpa [prefixWord, tailWord_3192892, baseEnd_3192892] using wordTrace_append hprefix tailTrace_3192892
  have hstable : (prefixWord ++ tailWord_3192892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192892).length < 2 ^ (prefixWord ++ tailWord_3192892).sum := by decide
  have hdescent : baseEnd_3192892 < baseStart_3192892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192893 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3192893 : Nat := 118140960795 + 3192893 * 2 ^ 59
def prefixEnd_3192893 : Nat := 4983230072969 + 3 ^ 40 * 3192893 * 2
def baseEnd_3192893 : Nat := 1639488787376081525153659

theorem tailTrace_3192893 : CollatzResearch.WordTrace tailWord_3192893 prefixEnd_3192893 1639488787376081525153659 := by
  unfold tailWord_3192893
  simp only [CollatzResearch.WordTrace]
  refine ⟨116454374821701438555743333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77636249881134292370495555 116454374821701438555743333)
  ·
    refine ⟨21835195279069019729201875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116454374821701438555743333 21835195279069019729201875)
    ·
      refine ⟨32752792918603529593802813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835195279069019729201875 32752792918603529593802813)
      ·
        refine ⟨12282297344476323597676055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32752792918603529593802813 12282297344476323597676055)
        ·
          refine ⟨18423446016714485396514083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282297344476323597676055 18423446016714485396514083)
          ·
            refine ⟨27635169025071728094771125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423446016714485396514083 27635169025071728094771125)
            ·
              refine ⟨2590797096100474508884793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27635169025071728094771125 2590797096100474508884793)
              ·
                refine ⟨1943097822075355881663595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590797096100474508884793 1943097822075355881663595)
                ·
                  refine ⟨2914646733113033822495393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943097822075355881663595 2914646733113033822495393)
                  ·
                    refine ⟨2185985049834775366871545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914646733113033822495393 2185985049834775366871545)
                    ·
                      refine ⟨1639488787376081525153659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185985049834775366871545 1639488787376081525153659)
                      ·
                        rfl

theorem cell23_3192893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3192893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192893 prefixEnd_3192893 := by exact prefixLift 3192893
  have htrace : WordTrace (prefixWord ++ tailWord_3192893) baseStart_3192893 baseEnd_3192893 := by
    simpa [prefixWord, tailWord_3192893, baseEnd_3192893] using wordTrace_append hprefix tailTrace_3192893
  have hstable : (prefixWord ++ tailWord_3192893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192893).length < 2 ^ (prefixWord ++ tailWord_3192893).sum := by decide
  have hdescent : baseEnd_3192893 < baseStart_3192893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192902 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3192902 : Nat := 118140960795 + 3192902 * 2 ^ 59
def prefixEnd_3192902 : Nat := 4983230072969 + 3 ^ 40 * 3192902 * 2
def baseEnd_3192902 : Nat := 1639493408701971989941117

theorem tailTrace_3192902 : CollatzResearch.WordTrace tailWord_3192902 prefixEnd_3192902 1639493408701971989941117 := by
  unfold tailWord_3192902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639209471208401034150655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77636468719112555395213973 3639209471208401034150655)
  ·
    refine ⟨5458814206812601551225983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3639209471208401034150655 5458814206812601551225983)
    ·
      refine ⟨8188221310218902326838975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5458814206812601551225983 8188221310218902326838975)
      ·
        refine ⟨12282331965328353490258463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8188221310218902326838975 12282331965328353490258463)
        ·
          refine ⟨18423497947992530235387695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282331965328353490258463 18423497947992530235387695)
          ·
            refine ⟨27635246921988795353081543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423497947992530235387695 27635246921988795353081543)
            ·
              refine ⟨41452870382983193029622315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27635246921988795353081543 41452870382983193029622315)
              ·
                refine ⟨62179305574474789544433473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41452870382983193029622315 62179305574474789544433473)
                ·
                  refine ⟨46634479180856092158325105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62179305574474789544433473 46634479180856092158325105)
                  ·
                    refine ⟨34975859385642069118743829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46634479180856092158325105 34975859385642069118743829)
                    ·
                      refine ⟨1639493408701971989941117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34975859385642069118743829 1639493408701971989941117)
                      ·
                        rfl

theorem cell23_3192902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3192902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192902 prefixEnd_3192902 := by exact prefixLift 3192902
  have htrace : WordTrace (prefixWord ++ tailWord_3192902) baseStart_3192902 baseEnd_3192902 := by
    simpa [prefixWord, tailWord_3192902, baseEnd_3192902] using wordTrace_append hprefix tailTrace_3192902
  have hstable : (prefixWord ++ tailWord_3192902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192902).length < 2 ^ (prefixWord ++ tailWord_3192902).sum := by decide
  have hdescent : baseEnd_3192902 < baseStart_3192902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192919 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_3192919 : Nat := 118140960795 + 3192919 * 2 ^ 59
def prefixEnd_3192919 : Nat := 4983230072969 + 3 ^ 40 * 3192919 * 2
def baseEnd_3192919 : Nat := 1639502137873098423428539

theorem tailTrace_3192919 : CollatzResearch.WordTrace tailWord_3192919 prefixEnd_3192919 1639502137873098423428539 := by
  unfold tailWord_3192919
  simp only [CollatzResearch.WordTrace]
  refine ⟨116455323119607244996189811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77636882079738163330793207 116455323119607244996189811)
  ·
    refine ⟨174682984679410867494284717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116455323119607244996189811 174682984679410867494284717)
    ·
      refine ⟨65506119254779075310356769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174682984679410867494284717 65506119254779075310356769)
      ·
        refine ⟨49129589441084306482767577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65506119254779075310356769 49129589441084306482767577)
        ·
          refine ⟨36847192080813229862075683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49129589441084306482767577 36847192080813229862075683)
          ·
            refine ⟨55270788121219844793113525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36847192080813229862075683 55270788121219844793113525)
            ·
              refine ⟨5181636386364360449354393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55270788121219844793113525 5181636386364360449354393)
              ·
                refine ⟨3886227289773270337015795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181636386364360449354393 3886227289773270337015795)
                ·
                  refine ⟨5829340934659905505523693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886227289773270337015795 5829340934659905505523693)
                  ·
                    refine ⟨2186002850497464564571385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5829340934659905505523693 2186002850497464564571385)
                    ·
                      refine ⟨1639502137873098423428539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186002850497464564571385 1639502137873098423428539)
                      ·
                        rfl

theorem cell23_3192919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_3192919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192919 prefixEnd_3192919 := by exact prefixLift 3192919
  have htrace : WordTrace (prefixWord ++ tailWord_3192919) baseStart_3192919 baseEnd_3192919 := by
    simpa [prefixWord, tailWord_3192919, baseEnd_3192919] using wordTrace_append hprefix tailTrace_3192919
  have hstable : (prefixWord ++ tailWord_3192919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192919).length < 2 ^ (prefixWord ++ tailWord_3192919).sum := by decide
  have hdescent : baseEnd_3192919 < baseStart_3192919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192932 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_3192932 : Nat := 118140960795 + 3192932 * 2 ^ 59
def prefixEnd_3192932 : Nat := 4983230072969 + 3 ^ 40 * 3192932 * 2
def baseEnd_3192932 : Nat := 1639508813121606872565979

theorem tailTrace_3192932 : CollatzResearch.WordTrace tailWord_3192932 prefixEnd_3192932 1639508813121606872565979 := by
  unfold tailWord_3192932
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227898634280074108206525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77637198179040098810942033 58227898634280074108206525)
  ·
    refine ⟨21835461987855027790577447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58227898634280074108206525 21835461987855027790577447)
    ·
      refine ⟨32753192981782541685866171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835461987855027790577447 32753192981782541685866171)
      ·
        refine ⟨49129789472673812528799257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32753192981782541685866171 49129789472673812528799257)
        ·
          refine ⟨36847342104505359396599443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49129789472673812528799257 36847342104505359396599443)
          ·
            refine ⟨55271013156758039094899165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36847342104505359396599443 55271013156758039094899165)
            ·
              refine ⟨20726629933784264660587187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55271013156758039094899165 20726629933784264660587187)
              ·
                refine ⟨31089944900676396990880781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20726629933784264660587187 31089944900676396990880781)
                ·
                  refine ⟨11658729337753648871580293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31089944900676396990880781 11658729337753648871580293)
                  ·
                    refine ⟨2186011750828809163421305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11658729337753648871580293 2186011750828809163421305)
                    ·
                      refine ⟨1639508813121606872565979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186011750828809163421305 1639508813121606872565979)
                      ·
                        rfl

theorem cell23_3192932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_3192932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192932 prefixEnd_3192932 := by exact prefixLift 3192932
  have htrace : WordTrace (prefixWord ++ tailWord_3192932) baseStart_3192932 baseEnd_3192932 := by
    simpa [prefixWord, tailWord_3192932, baseEnd_3192932] using wordTrace_append hprefix tailTrace_3192932
  have hstable : (prefixWord ++ tailWord_3192932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192932).length < 2 ^ (prefixWord ++ tailWord_3192932).sum := by decide
  have hdescent : baseEnd_3192932 < baseStart_3192932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192935 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3192935 : Nat := 118140960795 + 3192935 * 2 ^ 59
def prefixEnd_3192935 : Nat := 4983230072969 + 3 ^ 40 * 3192935 * 2
def baseEnd_3192935 : Nat := 1639510353563570360828465

theorem tailTrace_3192935 : CollatzResearch.WordTrace tailWord_3192935 prefixEnd_3192935 1639510353563570360828465 := by
  unfold tailWord_3192935
  simp only [CollatzResearch.WordTrace]
  refine ⟨116455906687549279728772259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77637271125032853152514839 116455906687549279728772259)
  ·
    refine ⟨174683860031323919593158389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116455906687549279728772259 174683860031323919593158389)
    ·
      refine ⟨16376611877936617461858599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174683860031323919593158389 16376611877936617461858599)
      ·
        refine ⟨24564917816904926192787899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376611877936617461858599 24564917816904926192787899)
        ·
          refine ⟨36847376725357389289181849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24564917816904926192787899 36847376725357389289181849)
          ·
            refine ⟨27635532544018041966886387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36847376725357389289181849 27635532544018041966886387)
            ·
              refine ⟨41453298816027062950329581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27635532544018041966886387 41453298816027062950329581)
              ·
                refine ⟨15544987056010148606373593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41453298816027062950329581 15544987056010148606373593)
                ·
                  refine ⟨11658740292007611454780195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15544987056010148606373593 11658740292007611454780195)
                  ·
                    refine ⟨17488110438011417182170293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11658740292007611454780195 17488110438011417182170293)
                    ·
                      refine ⟨1639510353563570360828465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17488110438011417182170293 1639510353563570360828465)
                      ·
                        rfl

theorem cell23_3192935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3192935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192935 prefixEnd_3192935 := by exact prefixLift 3192935
  have htrace : WordTrace (prefixWord ++ tailWord_3192935) baseStart_3192935 baseEnd_3192935 := by
    simpa [prefixWord, tailWord_3192935, baseEnd_3192935] using wordTrace_append hprefix tailTrace_3192935
  have hstable : (prefixWord ++ tailWord_3192935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192935).length < 2 ^ (prefixWord ++ tailWord_3192935).sum := by decide
  have hdescent : baseEnd_3192935 < baseStart_3192935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192945 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3192945 : Nat := 118140960795 + 3192945 * 2 ^ 59
def prefixEnd_3192945 : Nat := 4983230072969 + 3 ^ 40 * 3192945 * 2
def baseEnd_3192945 : Nat := 1639515488370115321703419

theorem tailTrace_3192945 : CollatzResearch.WordTrace tailWord_3192945 prefixEnd_3192945 1639515488370115321703419 := by
  unfold tailWord_3192945
  simp only [CollatzResearch.WordTrace]
  refine ⟨116456271417513051436636289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77637514278342034291090859 116456271417513051436636289)
  ·
    refine ⟨87342203563134788577477217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116456271417513051436636289 87342203563134788577477217)
    ·
      refine ⟨65506652672351091433107913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87342203563134788577477217 65506652672351091433107913)
      ·
        refine ⟨49129989504263318574830935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65506652672351091433107913 49129989504263318574830935)
        ·
          refine ⟨73694984256394977862246403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49129989504263318574830935 73694984256394977862246403)
          ·
            refine ⟨110542476384592466793369605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73694984256394977862246403 110542476384592466793369605)
            ·
              refine ⟨20726714322111087523756801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110542476384592466793369605 20726714322111087523756801)
              ·
                refine ⟨15545035741583315642817601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20726714322111087523756801 15545035741583315642817601)
                ·
                  refine ⟨11658776806187486732113201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15545035741583315642817601 11658776806187486732113201)
                  ·
                    refine ⟨8744082604640615049084901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11658776806187486732113201 8744082604640615049084901)
                    ·
                      refine ⟨1639515488370115321703419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8744082604640615049084901 1639515488370115321703419)
                      ·
                        rfl

theorem cell23_3192945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3192945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192945 prefixEnd_3192945 := by exact prefixLift 3192945
  have htrace : WordTrace (prefixWord ++ tailWord_3192945) baseStart_3192945 baseEnd_3192945 := by
    simpa [prefixWord, tailWord_3192945, baseEnd_3192945] using wordTrace_append hprefix tailTrace_3192945
  have hstable : (prefixWord ++ tailWord_3192945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192945).length < 2 ^ (prefixWord ++ tailWord_3192945).sum := by decide
  have hdescent : baseEnd_3192945 < baseStart_3192945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192989 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 5]
def baseStart_3192989 : Nat := 118140960795 + 3192989 * 2 ^ 59
def prefixEnd_3192989 : Nat := 4983230072969 + 3 ^ 40 * 3192989 * 2
def baseEnd_3192989 : Nat := 182170897946545905505913

theorem tailTrace_3192989 : CollatzResearch.WordTrace tailWord_3192989 prefixEnd_3192989 182170897946545905505913 := by
  unfold tailWord_3192989
  simp only [CollatzResearch.WordTrace]
  refine ⟨116457876229353646951238021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77638584152902431300825347 116457876229353646951238021)
  ·
    refine ⟨21835851793003808803357129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116457876229353646951238021 21835851793003808803357129)
    ·
      refine ⟨16376888844752856602517847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21835851793003808803357129 16376888844752856602517847)
      ·
        refine ⟨24565333267129284903776771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376888844752856602517847 24565333267129284903776771)
        ·
          refine ⟨36847999900693927355665157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24565333267129284903776771 36847999900693927355665157)
          ·
            refine ⟨6908999981380111379187217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36847999900693927355665157 6908999981380111379187217)
            ·
              refine ⟨5181749986035083534390413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908999981380111379187217 5181749986035083534390413)
              ·
                refine ⟨1943156244763156325396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5181749986035083534390413 1943156244763156325396405)
                ·
                  refine ⟨182170897946545905505913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943156244763156325396405 182170897946545905505913)
                  ·
                    rfl

theorem cell23_3192989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_3192989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192989 prefixEnd_3192989 := by exact prefixLift 3192989
  have htrace : WordTrace (prefixWord ++ tailWord_3192989) baseStart_3192989 baseEnd_3192989 := by
    simpa [prefixWord, tailWord_3192989, baseEnd_3192989] using wordTrace_append hprefix tailTrace_3192989
  have hstable : (prefixWord ++ tailWord_3192989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192989).length < 2 ^ (prefixWord ++ tailWord_3192989).sum := by decide
  have hdescent : baseEnd_3192989 < baseStart_3192989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193006 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_3193006 : Nat := 118140960795 + 3193006 * 2 ^ 59
def prefixEnd_3193006 : Nat := 4983230072969 + 3 ^ 40 * 3193006 * 2
def baseEnd_3193006 : Nat := 182171867854448842560071

theorem tailTrace_3193006 : CollatzResearch.WordTrace tailWord_3193006 prefixEnd_3193006 182171867854448842560071 := by
  unfold tailWord_3193006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557312033786507356825859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77638997513528039236404581 14557312033786507356825859)
  ·
    refine ⟨21835968050679761035238789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14557312033786507356825859 21835968050679761035238789)
    ·
      refine ⟨4094244009502455194107273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21835968050679761035238789 4094244009502455194107273)
      ·
        refine ⟨3070683007126841395580455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4094244009502455194107273 3070683007126841395580455)
        ·
          refine ⟨4606024510690262093370683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070683007126841395580455 4606024510690262093370683)
          ·
            refine ⟨6909036766035393140056025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606024510690262093370683 6909036766035393140056025)
            ·
              refine ⟨5181777574526544855042019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909036766035393140056025 5181777574526544855042019)
              ·
                refine ⟨7772666361789817282563029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181777574526544855042019 7772666361789817282563029)
                ·
                  refine ⟨182171867854448842560071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7772666361789817282563029 182171867854448842560071)
                  ·
                    rfl

theorem cell23_3193006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_3193006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193006 prefixEnd_3193006 := by exact prefixLift 3193006
  have htrace : WordTrace (prefixWord ++ tailWord_3193006) baseStart_3193006 baseEnd_3193006 := by
    simpa [prefixWord, tailWord_3193006, baseEnd_3193006] using wordTrace_append hprefix tailTrace_3193006
  have hstable : (prefixWord ++ tailWord_3193006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193006).length < 2 ^ (prefixWord ++ tailWord_3193006).sum := by decide
  have hdescent : baseEnd_3193006 < baseStart_3193006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193035 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_3193035 : Nat := 118140960795 + 3193035 * 2 ^ 59
def prefixEnd_3193035 : Nat := 4983230072969 + 3 ^ 40 * 3193035 * 2
def baseEnd_3193035 : Nat := 1639561701629019969578005

theorem tailTrace_3193035 : CollatzResearch.WordTrace tailWord_3193035 prefixEnd_3193035 1639561701629019969578005 := by
  unfold tailWord_3193035
  simp only [CollatzResearch.WordTrace]
  refine ⟨116459553987186996807412559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77639702658124664538275039 116459553987186996807412559)
  ·
    refine ⟨174689330980780495211118839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116459553987186996807412559 174689330980780495211118839)
    ·
      refine ⟨262033996471170742816678259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174689330980780495211118839 262033996471170742816678259)
      ·
        refine ⟨393050994706756114225017389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262033996471170742816678259 393050994706756114225017389)
        ·
          refine ⟨147394123015033542834381521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393050994706756114225017389 147394123015033542834381521)
          ·
            refine ⟨110545592261275157125786141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147394123015033542834381521 110545592261275157125786141)
            ·
              refine ⟨41454597097978183922169803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110545592261275157125786141 41454597097978183922169803)
              ·
                refine ⟨62181895646967275883254705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41454597097978183922169803 62181895646967275883254705)
                ·
                  refine ⟨46636421735225456912441029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62181895646967275883254705 46636421735225456912441029)
                  ·
                    refine ⟨8744329075354773171082693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46636421735225456912441029 8744329075354773171082693)
                    ·
                      refine ⟨1639561701629019969578005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8744329075354773171082693 1639561701629019969578005)
                      ·
                        rfl

theorem cell23_3193035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_3193035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193035 prefixEnd_3193035 := by exact prefixLift 3193035
  have htrace : WordTrace (prefixWord ++ tailWord_3193035) baseStart_3193035 baseEnd_3193035 := by
    simpa [prefixWord, tailWord_3193035, baseEnd_3193035] using wordTrace_append hprefix tailTrace_3193035
  have hstable : (prefixWord ++ tailWord_3193035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193035).length < 2 ^ (prefixWord ++ tailWord_3193035).sum := by decide
  have hdescent : baseEnd_3193035 < baseStart_3193035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193089 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3193089 : Nat := 118140960795 + 3193089 * 2 ^ 59
def prefixEnd_3193089 : Nat := 4983230072969 + 3 ^ 40 * 3193089 * 2
def baseEnd_3193089 : Nat := 1639589429584362758302757

theorem tailTrace_3193089 : CollatzResearch.WordTrace tailWord_3193089 prefixEnd_3193089 1639589429584362758302757 := by
  unfold tailWord_3193089
  simp only [CollatzResearch.WordTrace]
  refine ⟨116461523528991364029878321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77641015685994242686585547 116461523528991364029878321)
  ·
    refine ⟨87346142646743523022408741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116461523528991364029878321 87346142646743523022408741)
    ·
      refine ⟨16377401746264410566701639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87346142646743523022408741 16377401746264410566701639)
      ·
        refine ⟨24566102619396615850052459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16377401746264410566701639 24566102619396615850052459)
        ·
          refine ⟨36849153929094923775078689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24566102619396615850052459 36849153929094923775078689)
          ·
            refine ⟨27636865446821192831309017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36849153929094923775078689 27636865446821192831309017)
            ·
              refine ⟨20727649085115894623481763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27636865446821192831309017 20727649085115894623481763)
              ·
                refine ⟨31091473627673841935222645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20727649085115894623481763 31091473627673841935222645)
                ·
                  refine ⟨2914825652594422681427123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31091473627673841935222645 2914825652594422681427123)
                  ·
                    refine ⟨4372238478891634022140685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914825652594422681427123 4372238478891634022140685)
                    ·
                      refine ⟨1639589429584362758302757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4372238478891634022140685 1639589429584362758302757)
                      ·
                        rfl

theorem cell23_3193089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3193089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193089 prefixEnd_3193089 := by exact prefixLift 3193089
  have htrace : WordTrace (prefixWord ++ tailWord_3193089) baseStart_3193089 baseEnd_3193089 := by
    simpa [prefixWord, tailWord_3193089, baseEnd_3193089] using wordTrace_append hprefix tailTrace_3193089
  have hstable : (prefixWord ++ tailWord_3193089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193089).length < 2 ^ (prefixWord ++ tailWord_3193089).sum := by decide
  have hdescent : baseEnd_3193089 < baseStart_3193089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193117 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_3193117 : Nat := 118140960795 + 3193117 * 2 ^ 59
def prefixEnd_3193117 : Nat := 4983230072969 + 3 ^ 40 * 3193117 * 2
def baseEnd_3193117 : Nat := 546534602347562882917543

theorem tailTrace_3193117 : CollatzResearch.WordTrace tailWord_3193117 prefixEnd_3193117 546534602347562882917543 := by
  unfold tailWord_3193117
  simp only [CollatzResearch.WordTrace]
  refine ⟨116462544772889924811897605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77641696515259949874598403 116462544772889924811897605)
  ·
    refine ⟨21836727144916860902230801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116462544772889924811897605 21836727144916860902230801)
    ·
      refine ⟨16377545358687645676673101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21836727144916860902230801 16377545358687645676673101)
      ·
        refine ⟨6141579509507867128752413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16377545358687645676673101 6141579509507867128752413)
        ·
          refine ⟨2303092316065450173282155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6141579509507867128752413 2303092316065450173282155)
          ·
            refine ⟨3454638474098175259923233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303092316065450173282155 3454638474098175259923233)
            ·
              refine ⟨2590978855573631444942425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454638474098175259923233 2590978855573631444942425)
              ·
                refine ⟨1943234141680223583706819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590978855573631444942425 1943234141680223583706819)
                ·
                  refine ⟨2914851212520335375560229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943234141680223583706819 2914851212520335375560229)
                  ·
                    refine ⟨546534602347562882917543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914851212520335375560229 546534602347562882917543)
                    ·
                      rfl

theorem cell23_3193117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_3193117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193117 prefixEnd_3193117 := by exact prefixLift 3193117
  have htrace : WordTrace (prefixWord ++ tailWord_3193117) baseStart_3193117 baseEnd_3193117 := by
    simpa [prefixWord, tailWord_3193117, baseEnd_3193117] using wordTrace_append hprefix tailTrace_3193117
  have hstable : (prefixWord ++ tailWord_3193117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193117).length < 2 ^ (prefixWord ++ tailWord_3193117).sum := by decide
  have hdescent : baseEnd_3193117 < baseStart_3193117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193132 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3193132 : Nat := 118140960795 + 3193132 * 2 ^ 59
def prefixEnd_3193132 : Nat := 4983230072969 + 3 ^ 40 * 3193132 * 2
def baseEnd_3193132 : Nat := 1639611509252506090065059

theorem tailTrace_3193132 : CollatzResearch.WordTrace tailWord_3193132 prefixEnd_3193132 1639611509252506090065059 := by
  unfold tailWord_3193132
  simp only [CollatzResearch.WordTrace]
  refine ⟨58231545933917791186846825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77642061245223721582462433 58231545933917791186846825)
  ·
    refine ⟨43673659450438343390135119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58231545933917791186846825 43673659450438343390135119)
    ·
      refine ⟨65510489175657515085202679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43673659450438343390135119 65510489175657515085202679)
      ·
        refine ⟨98265733763486272627804019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65510489175657515085202679 98265733763486272627804019)
        ·
          refine ⟨147398600645229408941706029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98265733763486272627804019 147398600645229408941706029)
          ·
            refine ⟨55274475241961028353139761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147398600645229408941706029 55274475241961028353139761)
            ·
              refine ⟨41455856431470771264854821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55274475241961028353139761 41455856431470771264854821)
              ·
                refine ⟨7772973080900769612160279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41455856431470771264854821 7772973080900769612160279)
                ·
                  refine ⟨11659459621351154418240419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7772973080900769612160279 11659459621351154418240419)
                  ·
                    refine ⟨17489189432026731627360629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11659459621351154418240419 17489189432026731627360629)
                    ·
                      refine ⟨1639611509252506090065059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17489189432026731627360629 1639611509252506090065059)
                      ·
                        rfl

theorem cell23_3193132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3193132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193132 prefixEnd_3193132 := by exact prefixLift 3193132
  have htrace : WordTrace (prefixWord ++ tailWord_3193132) baseStart_3193132 baseEnd_3193132 := by
    simpa [prefixWord, tailWord_3193132, baseEnd_3193132] using wordTrace_append hprefix tailTrace_3193132
  have hstable : (prefixWord ++ tailWord_3193132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193132).length < 2 ^ (prefixWord ++ tailWord_3193132).sum := by decide
  have hdescent : baseEnd_3193132 < baseStart_3193132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193139 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 2, 4]
def baseStart_3193139 : Nat := 118140960795 + 3193139 * 2 ^ 59
def prefixEnd_3193139 : Nat := 4983230072969 + 3 ^ 40 * 3193139 * 2
def baseEnd_3193139 : Nat := 546538367872362520892509

theorem tailTrace_3193139 : CollatzResearch.WordTrace tailWord_3193139 prefixEnd_3193139 546538367872362520892509 := by
  unfold tailWord_3193139
  simp only [CollatzResearch.WordTrace]
  refine ⟨116463347178810222569198471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77642231452540148379465647 116463347178810222569198471)
  ·
    refine ⟨174695020768215333853797707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116463347178810222569198471 174695020768215333853797707)
    ·
      refine ⟨262042531152323000780696561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174695020768215333853797707 262042531152323000780696561)
      ·
        refine ⟨196531898364242250585522421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262042531152323000780696561 196531898364242250585522421)
        ·
          refine ⟨18424865471647710992392727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196531898364242250585522421 18424865471647710992392727)
          ·
            refine ⟨27637298207471566488589091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18424865471647710992392727 27637298207471566488589091)
            ·
              refine ⟨41455947311207349732883637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27637298207471566488589091 41455947311207349732883637)
              ·
                refine ⟨3886495060425689037457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41455947311207349732883637 3886495060425689037457841)
                ·
                  refine ⟨2914871295319266778093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886495060425689037457841 2914871295319266778093381)
                  ·
                    refine ⟨546538367872362520892509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914871295319266778093381 546538367872362520892509)
                    ·
                      rfl

theorem cell23_3193139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 4].length) (baseStart_3193139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193139 prefixEnd_3193139 := by exact prefixLift 3193139
  have htrace : WordTrace (prefixWord ++ tailWord_3193139) baseStart_3193139 baseEnd_3193139 := by
    simpa [prefixWord, tailWord_3193139, baseEnd_3193139] using wordTrace_append hprefix tailTrace_3193139
  have hstable : (prefixWord ++ tailWord_3193139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193139).length < 2 ^ (prefixWord ++ tailWord_3193139).sum := by decide
  have hdescent : baseEnd_3193139 < baseStart_3193139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193146 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_3193146 : Nat := 118140960795 + 3193146 * 2 ^ 59
def prefixEnd_3193146 : Nat := 4983230072969 + 3 ^ 40 * 3193146 * 2
def baseEnd_3193146 : Nat := 1639618697981669035289995

theorem tailTrace_3193146 : CollatzResearch.WordTrace tailWord_3193146 prefixEnd_3193146 1639618697981669035289995 := by
  unfold tailWord_3193146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115900622446215691175823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77642401659856575176468861 29115900622446215691175823)
  ·
    refine ⟨43673850933669323536763735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29115900622446215691175823 43673850933669323536763735)
    ·
      refine ⟨65510776400503985305145603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43673850933669323536763735 65510776400503985305145603)
      ·
        refine ⟨98266164600755977957718405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65510776400503985305145603 98266164600755977957718405)
        ·
          refine ⟨18424905862641745867072201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98266164600755977957718405 18424905862641745867072201)
          ·
            refine ⟨13818679396981309400304151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18424905862641745867072201 13818679396981309400304151)
            ·
              refine ⟨20728019095471964100456227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818679396981309400304151 20728019095471964100456227)
              ·
                refine ⟨31092028643207946150684341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20728019095471964100456227 31092028643207946150684341)
                ·
                  refine ⟨2914877685300744951626657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31092028643207946150684341 2914877685300744951626657)
                  ·
                    refine ⟨2186158263975558713719993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914877685300744951626657 2186158263975558713719993)
                    ·
                      refine ⟨1639618697981669035289995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186158263975558713719993 1639618697981669035289995)
                      ·
                        rfl

theorem cell23_3193146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_3193146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193146 prefixEnd_3193146 := by exact prefixLift 3193146
  have htrace : WordTrace (prefixWord ++ tailWord_3193146) baseStart_3193146 baseEnd_3193146 := by
    simpa [prefixWord, tailWord_3193146, baseEnd_3193146] using wordTrace_append hprefix tailTrace_3193146
  have hstable : (prefixWord ++ tailWord_3193146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193146).length < 2 ^ (prefixWord ++ tailWord_3193146).sum := by decide
  have hdescent : baseEnd_3193146 < baseStart_3193146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193173 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_3193173 : Nat := 118140960795 + 3193173 * 2 ^ 59
def prefixEnd_3193173 : Nat := 4983230072969 + 3 ^ 40 * 3193173 * 2
def baseEnd_3193173 : Nat := 546544187319780143217457

theorem tailTrace_3193173 : CollatzResearch.WordTrace tailWord_3193173 prefixEnd_3193173 546544187319780143217457 := by
  unfold tailWord_3193173
  simp only [CollatzResearch.WordTrace]
  refine ⟨116464587260687046375936173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77643058173791364250624115 116464587260687046375936173)
  ·
    refine ⟨43674220222757642390976065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116464587260687046375936173 43674220222757642390976065)
    ·
      refine ⟨32755665167068231793232049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43674220222757642390976065 32755665167068231793232049)
      ·
        refine ⟨24566748875301173844924037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32755665167068231793232049 24566748875301173844924037)
        ·
          refine ⟨4606265414118970095923257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24566748875301173844924037 4606265414118970095923257)
          ·
            refine ⟨3454699060589227571942443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606265414118970095923257 3454699060589227571942443)
            ·
              refine ⟨5182048590883841357913665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454699060589227571942443 5182048590883841357913665)
              ·
                refine ⟨3886536443162881018435249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182048590883841357913665 3886536443162881018435249)
                ·
                  refine ⟨2914902332372160763826437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886536443162881018435249 2914902332372160763826437)
                  ·
                    refine ⟨546544187319780143217457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914902332372160763826437 546544187319780143217457)
                    ·
                      rfl

theorem cell23_3193173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_3193173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193173 prefixEnd_3193173 := by exact prefixLift 3193173
  have htrace : WordTrace (prefixWord ++ tailWord_3193173) baseStart_3193173 baseEnd_3193173 := by
    simpa [prefixWord, tailWord_3193173, baseEnd_3193173] using wordTrace_append hprefix tailTrace_3193173
  have hstable : (prefixWord ++ tailWord_3193173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193173).length < 2 ^ (prefixWord ++ tailWord_3193173).sum := by decide
  have hdescent : baseEnd_3193173 < baseStart_3193173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193212 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3193212 : Nat := 118140960795 + 3193212 * 2 ^ 59
def prefixEnd_3193212 : Nat := 4983230072969 + 3 ^ 40 * 3193212 * 2
def baseEnd_3193212 : Nat := 546550862568288592354897

theorem tailTrace_3193212 : CollatzResearch.WordTrace tailWord_3193212 prefixEnd_3193212 546550862568288592354897 := by
  unfold tailWord_3193212
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233004853772878018302945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77644006471697170691070593 58233004853772878018302945)
  ·
    refine ⟨43674753640329658513727209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58233004853772878018302945 43674753640329658513727209)
    ·
      refine ⟨32756065230247243885295407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43674753640329658513727209 32756065230247243885295407)
      ·
        refine ⟨49134097845370865827943111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32756065230247243885295407 49134097845370865827943111)
        ·
          refine ⟨73701146768056298741914667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49134097845370865827943111 73701146768056298741914667)
          ·
            refine ⟨110551720152084448112872001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73701146768056298741914667 110551720152084448112872001)
            ·
              refine ⟨82913790114063336084654001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110551720152084448112872001 82913790114063336084654001)
              ·
                refine ⟨62185342585547502063490501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82913790114063336084654001 62185342585547502063490501)
                ·
                  refine ⟨11659751734790156636904469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62185342585547502063490501 11659751734790156636904469)
                  ·
                    refine ⟨546550862568288592354897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11659751734790156636904469 546550862568288592354897)
                    ·
                      rfl

theorem cell23_3193212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3193212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193212 prefixEnd_3193212 := by exact prefixLift 3193212
  have htrace : WordTrace (prefixWord ++ tailWord_3193212) baseStart_3193212 baseEnd_3193212 := by
    simpa [prefixWord, tailWord_3193212, baseEnd_3193212] using wordTrace_append hprefix tailTrace_3193212
  have hstable : (prefixWord ++ tailWord_3193212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193212).length < 2 ^ (prefixWord ++ tailWord_3193212).sum := by decide
  have hdescent : baseEnd_3193212 < baseStart_3193212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193232 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_3193232 : Nat := 118140960795 + 3193232 * 2 ^ 59
def prefixEnd_3193232 : Nat := 4983230072969 + 3 ^ 40 * 3193232 * 2
def baseEnd_3193232 : Nat := 1639662857317955698814599

theorem tailTrace_3193232 : CollatzResearch.WordTrace tailWord_3193232 prefixEnd_3193232 1639662857317955698814599 := by
  unfold tailWord_3193232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233369583736649726166975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77644492778315532968222633 58233369583736649726166975)
  ·
    refine ⟨87350054375604974589250463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58233369583736649726166975 87350054375604974589250463)
    ·
      refine ⟨131025081563407461883875695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87350054375604974589250463 131025081563407461883875695)
      ·
        refine ⟨196537622345111192825813543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131025081563407461883875695 196537622345111192825813543)
        ·
          refine ⟨294806433517666789238720315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196537622345111192825813543 294806433517666789238720315)
          ·
            refine ⟨442209650276500183858080473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294806433517666789238720315 442209650276500183858080473)
            ·
              refine ⟨331657237707375137893560355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442209650276500183858080473 331657237707375137893560355)
              ·
                refine ⟨497485856561062706840340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331657237707375137893560355 497485856561062706840340533)
                ·
                  refine ⟨46639299052599628766281925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497485856561062706840340533 46639299052599628766281925)
                  ·
                    refine ⟨8744868572362430393677861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46639299052599628766281925 8744868572362430393677861)
                    ·
                      refine ⟨1639662857317955698814599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8744868572362430393677861 1639662857317955698814599)
                      ·
                        rfl

theorem cell23_3193232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_3193232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193232 prefixEnd_3193232 := by exact prefixLift 3193232
  have htrace : WordTrace (prefixWord ++ tailWord_3193232) baseStart_3193232 baseEnd_3193232 := by
    simpa [prefixWord, tailWord_3193232, baseEnd_3193232] using wordTrace_append hprefix tailTrace_3193232
  have hstable : (prefixWord ++ tailWord_3193232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193232).length < 2 ^ (prefixWord ++ tailWord_3193232).sum := by decide
  have hdescent : baseEnd_3193232 < baseStart_3193232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193253 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_3193253 : Nat := 118140960795 + 3193253 * 2 ^ 59
def prefixEnd_3193253 : Nat := 4983230072969 + 3 ^ 40 * 3193253 * 2
def baseEnd_3193253 : Nat := 1639673640411700116652003

theorem tailTrace_3193253 : CollatzResearch.WordTrace tailWord_3193253 prefixEnd_3193253 1639673640411700116652003 := by
  unfold tailWord_3193253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116467505100397220038848413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77645003400264813359232275 116467505100397220038848413)
  ·
    refine ⟨43675314412648957514568155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116467505100397220038848413 43675314412648957514568155)
    ·
      refine ⟨65512971618973436271852233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43675314412648957514568155 65512971618973436271852233)
      ·
        refine ⟨49134728714230077203889175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65512971618973436271852233 49134728714230077203889175)
        ·
          refine ⟨73702093071345115805833763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49134728714230077203889175 73702093071345115805833763)
          ·
            refine ⟨110553139607017673708750645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73702093071345115805833763 110553139607017673708750645)
            ·
              refine ⟨10364356838157906910195373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110553139607017673708750645 10364356838157906910195373)
              ·
                refine ⟨3886633814309215091323265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10364356838157906910195373 3886633814309215091323265)
                ·
                  refine ⟨2914975360731911318492449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886633814309215091323265 2914975360731911318492449)
                  ·
                    refine ⟨2186231520548933488869337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914975360731911318492449 2186231520548933488869337)
                    ·
                      refine ⟨1639673640411700116652003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186231520548933488869337 1639673640411700116652003)
                      ·
                        rfl

theorem cell23_3193253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_3193253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193253 prefixEnd_3193253 := by exact prefixLift 3193253
  have htrace : WordTrace (prefixWord ++ tailWord_3193253) baseStart_3193253 baseEnd_3193253 := by
    simpa [prefixWord, tailWord_3193253, baseEnd_3193253] using wordTrace_append hprefix tailTrace_3193253
  have hstable : (prefixWord ++ tailWord_3193253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193253).length < 2 ^ (prefixWord ++ tailWord_3193253).sum := by decide
  have hdescent : baseEnd_3193253 < baseStart_3193253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193256 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3193256 : Nat := 118140960795 + 3193256 * 2 ^ 59
def prefixEnd_3193256 : Nat := 4983230072969 + 3 ^ 40 * 3193256 * 2
def baseEnd_3193256 : Nat := 1639675180853663604914489

theorem tailTrace_3193256 : CollatzResearch.WordTrace tailWord_3193256 prefixEnd_3193256 1639675180853663604914489 := by
  unfold tailWord_3193256
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233807259693175775603811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77645076346257567700805081 58233807259693175775603811)
  ·
    refine ⟨87350710889539763663405717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58233807259693175775603811 87350710889539763663405717)
    ·
      refine ⟨4094564572947176421722143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87350710889539763663405717 4094564572947176421722143)
      ·
        refine ⟨6141846859420764632583215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094564572947176421722143 6141846859420764632583215)
        ·
          refine ⟨9212770289131146948874823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141846859420764632583215 9212770289131146948874823)
          ·
            refine ⟨13819155433696720423312235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212770289131146948874823 13819155433696720423312235)
            ·
              refine ⟨20728733150545080634968353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13819155433696720423312235 20728733150545080634968353)
              ·
                refine ⟨15546549862908810476226265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20728733150545080634968353 15546549862908810476226265)
                ·
                  refine ⟨11659912397181607857169699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15546549862908810476226265 11659912397181607857169699)
                  ·
                    refine ⟨17489868595772411785754549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11659912397181607857169699 17489868595772411785754549)
                    ·
                      refine ⟨1639675180853663604914489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17489868595772411785754549 1639675180853663604914489)
                      ·
                        rfl

theorem cell23_3193256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3193256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193256 prefixEnd_3193256 := by exact prefixLift 3193256
  have htrace : WordTrace (prefixWord ++ tailWord_3193256) baseStart_3193256 baseEnd_3193256 := by
    simpa [prefixWord, tailWord_3193256, baseEnd_3193256] using wordTrace_append hprefix tailTrace_3193256
  have hstable : (prefixWord ++ tailWord_3193256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193256).length < 2 ^ (prefixWord ++ tailWord_3193256).sum := by decide
  have hdescent : baseEnd_3193256 < baseStart_3193256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193289 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_3193289 : Nat := 118140960795 + 3193289 * 2 ^ 59
def prefixEnd_3193289 : Nat := 4983230072969 + 3 ^ 40 * 3193289 * 2
def baseEnd_3193289 : Nat := 546564041905087325267279

theorem tailTrace_3193289 : CollatzResearch.WordTrace tailWord_3193289 prefixEnd_3193289 546564041905087325267279 := by
  unfold tailWord_3193289
  simp only [CollatzResearch.WordTrace]
  refine ⟨116468818128266798187158921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77645878752177865458105947 116468818128266798187158921)
  ·
    refine ⟨87351613596200098640369191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116468818128266798187158921 87351613596200098640369191)
    ·
      refine ⟨131027420394300147960553787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87351613596200098640369191 131027420394300147960553787)
      ·
        refine ⟨196541130591450221940830681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131027420394300147960553787 196541130591450221940830681)
        ·
          refine ⟨147405847943587666455623011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196541130591450221940830681 147405847943587666455623011)
          ·
            refine ⟨221108771915381499683434517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147405847943587666455623011 221108771915381499683434517)
            ·
              refine ⟨10364473683533507797660993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221108771915381499683434517 10364473683533507797660993)
              ·
                refine ⟨7773355262650130848245745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10364473683533507797660993 7773355262650130848245745)
                ·
                  refine ⟨5830016446987598136184309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7773355262650130848245745 5830016446987598136184309)
                  ·
                    refine ⟨546564041905087325267279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5830016446987598136184309 546564041905087325267279)
                    ·
                      rfl

theorem cell23_3193289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_3193289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193289 prefixEnd_3193289 := by exact prefixLift 3193289
  have htrace : WordTrace (prefixWord ++ tailWord_3193289) baseStart_3193289 baseEnd_3193289 := by
    simpa [prefixWord, tailWord_3193289, baseEnd_3193289] using wordTrace_append hprefix tailTrace_3193289
  have hstable : (prefixWord ++ tailWord_3193289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193289).length < 2 ^ (prefixWord ++ tailWord_3193289).sum := by decide
  have hdescent : baseEnd_3193289 < baseStart_3193289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193326 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3193326 : Nat := 118140960795 + 3193326 * 2 ^ 59
def prefixEnd_3193326 : Nat := 4983230072969 + 3 ^ 40 * 3193326 * 2
def baseEnd_3193326 : Nat := 1639711124499478331039167

theorem tailTrace_3193326 : CollatzResearch.WordTrace tailWord_3193326 prefixEnd_3193326 1639711124499478331039167 := by
  unfold tailWord_3193326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558770953641594188281979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77646778419421835670837221 14558770953641594188281979)
  ·
    refine ⟨21838156430462391282422969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14558770953641594188281979 21838156430462391282422969)
    ·
      refine ⟨16378617322846793461817227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21838156430462391282422969 16378617322846793461817227)
      ·
        refine ⟨24567925984270190192725841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378617322846793461817227 24567925984270190192725841)
        ·
          refine ⟨18425944488202642644544381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24567925984270190192725841 18425944488202642644544381)
          ·
            refine ⟨6909729183075990991704143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18425944488202642644544381 6909729183075990991704143)
            ·
              refine ⟨10364593774613986487556215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909729183075990991704143 10364593774613986487556215)
              ·
                refine ⟨15546890661920979731334323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10364593774613986487556215 15546890661920979731334323)
                ·
                  refine ⟨23320335992881469597001485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15546890661920979731334323 23320335992881469597001485)
                  ·
                    refine ⟨8745125997330551098875557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23320335992881469597001485 8745125997330551098875557)
                    ·
                      refine ⟨1639711124499478331039167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8745125997330551098875557 1639711124499478331039167)
                      ·
                        rfl

theorem cell23_3193326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3193326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193326 prefixEnd_3193326 := by exact prefixLift 3193326
  have htrace : WordTrace (prefixWord ++ tailWord_3193326) baseStart_3193326 baseEnd_3193326 := by
    simpa [prefixWord, tailWord_3193326, baseEnd_3193326] using wordTrace_append hprefix tailTrace_3193326
  have hstable : (prefixWord ++ tailWord_3193326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193326).length < 2 ^ (prefixWord ++ tailWord_3193326).sum := by decide
  have hdescent : baseEnd_3193326 < baseStart_3193326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193359 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_3193359 : Nat := 118140960795 + 3193359 * 2 ^ 59
def prefixEnd_3193359 : Nat := 4983230072969 + 3 ^ 40 * 3193359 * 2
def baseEnd_3193359 : Nat := 1639728069361076701926515

theorem tailTrace_3193359 : CollatzResearch.WordTrace tailWord_3193359 prefixEnd_3193359 1639728069361076701926515 := by
  unfold tailWord_3193359
  simp only [CollatzResearch.WordTrace]
  refine ⟨116471371238013200142207131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77647580825342133428138087 116471371238013200142207131)
  ·
    refine ⟨174707056857019800213310697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116471371238013200142207131 174707056857019800213310697)
    ·
      refine ⟨131030292642764850159983023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174707056857019800213310697 131030292642764850159983023)
      ·
        refine ⟨196545438964147275239974535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131030292642764850159983023 196545438964147275239974535)
        ·
          refine ⟨294818158446220912859961803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196545438964147275239974535 294818158446220912859961803)
          ·
            refine ⟨442227237669331369289942705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294818158446220912859961803 442227237669331369289942705)
            ·
              refine ⟨331670428251998526967457029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442227237669331369289942705 331670428251998526967457029)
              ·
                refine ⟨62188205297249723806398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331670428251998526967457029 62188205297249723806398193)
                ·
                  refine ⟨46641153972937292854798645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62188205297249723806398193 46641153972937292854798645)
                  ·
                    refine ⟨4372608184962871205137373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46641153972937292854798645 4372608184962871205137373)
                    ·
                      refine ⟨1639728069361076701926515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4372608184962871205137373 1639728069361076701926515)
                      ·
                        rfl

theorem cell23_3193359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_3193359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193359 prefixEnd_3193359 := by exact prefixLift 3193359
  have htrace : WordTrace (prefixWord ++ tailWord_3193359) baseStart_3193359 baseEnd_3193359 := by
    simpa [prefixWord, tailWord_3193359, baseEnd_3193359] using wordTrace_append hprefix tailTrace_3193359
  have hstable : (prefixWord ++ tailWord_3193359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193359).length < 2 ^ (prefixWord ++ tailWord_3193359).sum := by decide
  have hdescent : baseEnd_3193359 < baseStart_3193359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193426 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3193426 : Nat := 118140960795 + 3193426 * 2 ^ 59
def prefixEnd_3193426 : Nat := 4983230072969 + 3 ^ 40 * 3193426 * 2
def baseEnd_3193426 : Nat := 546587490854975979929569

theorem tailTrace_3193426 : CollatzResearch.WordTrace tailWord_3193426 prefixEnd_3193426 546587490854975979929569 := by
  unfold tailWord_3193426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29118453732192617646224033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77649209952513647056597421 29118453732192617646224033)
  ·
    refine ⟨21838840299144463234668025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29118453732192617646224033 21838840299144463234668025)
    ·
      refine ⟨16379130224358347426001019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21838840299144463234668025 16379130224358347426001019)
      ·
        refine ⟨24568695336537521139001529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379130224358347426001019 24568695336537521139001529)
        ·
          refine ⟨18426521502403140854251147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24568695336537521139001529 18426521502403140854251147)
          ·
            refine ⟨27639782253604711281376721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18426521502403140854251147 27639782253604711281376721)
            ·
              refine ⟨20729836690203533461032541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27639782253604711281376721 20729836690203533461032541)
              ·
                refine ⟨7773688758826325047887203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20729836690203533461032541 7773688758826325047887203)
                ·
                  refine ⟨11660533138239487571830805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773688758826325047887203 11660533138239487571830805)
                  ·
                    refine ⟨546587490854975979929569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11660533138239487571830805 546587490854975979929569)
                    ·
                      rfl

theorem cell23_3193426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3193426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193426 prefixEnd_3193426 := by exact prefixLift 3193426
  have htrace : WordTrace (prefixWord ++ tailWord_3193426) baseStart_3193426 baseEnd_3193426 := by
    simpa [prefixWord, tailWord_3193426, baseEnd_3193426] using wordTrace_append hprefix tailTrace_3193426
  have hstable : (prefixWord ++ tailWord_3193426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193426).length < 2 ^ (prefixWord ++ tailWord_3193426).sum := by decide
  have hdescent : baseEnd_3193426 < baseStart_3193426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193450 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3193450 : Nat := 118140960795 + 3193450 * 2 ^ 59
def prefixEnd_3193450 : Nat := 4983230072969 + 3 ^ 40 * 3193450 * 2
def baseEnd_3193450 : Nat := 1639774796100635845888597

theorem tailTrace_3193450 : CollatzResearch.WordTrace tailWord_3193450 prefixEnd_3193450 1639774796100635845888597 := by
  unfold tailWord_3193450
  simp only [CollatzResearch.WordTrace]
  refine ⟨29118672570170880670942451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77649793520455681789179869 29118672570170880670942451)
  ·
    refine ⟨43678008855256321006413677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29118672570170880670942451 43678008855256321006413677)
    ·
      refine ⟨16379253320721120377405129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43678008855256321006413677 16379253320721120377405129)
      ·
        refine ⟨12284439990540840283053847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16379253320721120377405129 12284439990540840283053847)
        ·
          refine ⟨18426659985811260424580771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284439990540840283053847 18426659985811260424580771)
          ·
            refine ⟨27639989978716890636871157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18426659985811260424580771 27639989978716890636871157)
            ·
              refine ⟨2591249060504708497206671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27639989978716890636871157 2591249060504708497206671)
              ·
                refine ⟨3886873590757062745810007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591249060504708497206671 3886873590757062745810007)
                ·
                  refine ⟨5830310386135594118715011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886873590757062745810007 5830310386135594118715011)
                  ·
                    refine ⟨8745465579203391178072517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5830310386135594118715011 8745465579203391178072517)
                    ·
                      refine ⟨1639774796100635845888597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8745465579203391178072517 1639774796100635845888597)
                      ·
                        rfl

theorem cell23_3193450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3193450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193450 prefixEnd_3193450 := by exact prefixLift 3193450
  have htrace : WordTrace (prefixWord ++ tailWord_3193450) baseStart_3193450 baseEnd_3193450 := by
    simpa [prefixWord, tailWord_3193450, baseEnd_3193450] using wordTrace_append hprefix tailTrace_3193450
  have hstable : (prefixWord ++ tailWord_3193450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193450).length < 2 ^ (prefixWord ++ tailWord_3193450).sum := by decide
  have hdescent : baseEnd_3193450 < baseStart_3193450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193453 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3193453 : Nat := 118140960795 + 3193453 * 2 ^ 59
def prefixEnd_3193453 : Nat := 4983230072969 + 3 ^ 40 * 3193453 * 2
def baseEnd_3193453 : Nat := 1639776336542599334151083

theorem tailTrace_3193453 : CollatzResearch.WordTrace tailWord_3193453 prefixEnd_3193453 1639776336542599334151083 := by
  unfold tailWord_3193453
  simp only [CollatzResearch.WordTrace]
  refine ⟨116474799699672654196129013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77649866466448436130752675 116474799699672654196129013)
  ·
    refine ⟨10919512471844311330887095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116474799699672654196129013 10919512471844311330887095)
    ·
      refine ⟨16379268707766466996330643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919512471844311330887095 16379268707766466996330643)
      ·
        refine ⟨24568903061649700494495965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379268707766466996330643 24568903061649700494495965)
        ·
          refine ⟨9213338648118637685435987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24568903061649700494495965 9213338648118637685435987)
          ·
            refine ⟨13820007972177956528153981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9213338648118637685435987 13820007972177956528153981)
            ·
              refine ⟨5182502989566733698057743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13820007972177956528153981 5182502989566733698057743)
              ·
                refine ⟨7773754484350100547086615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182502989566733698057743 7773754484350100547086615)
                ·
                  refine ⟨11660631726525150820629923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773754484350100547086615 11660631726525150820629923)
                  ·
                    refine ⟨17490947589787726230944885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11660631726525150820629923 17490947589787726230944885)
                    ·
                      refine ⟨1639776336542599334151083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17490947589787726230944885 1639776336542599334151083)
                      ·
                        rfl

theorem cell23_3193453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3193453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193453 prefixEnd_3193453 := by exact prefixLift 3193453
  have htrace : WordTrace (prefixWord ++ tailWord_3193453) baseStart_3193453 baseEnd_3193453 := by
    simpa [prefixWord, tailWord_3193453, baseEnd_3193453] using wordTrace_append hprefix tailTrace_3193453
  have hstable : (prefixWord ++ tailWord_3193453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193453).length < 2 ^ (prefixWord ++ tailWord_3193453).sum := by decide
  have hdescent : baseEnd_3193453 < baseStart_3193453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193456 : List Nat := [2, 1, 1, 1, 8, 10]
def baseStart_3193456 : Nat := 118140960795 + 3193456 * 2 ^ 59
def prefixEnd_3193456 : Nat := 4983230072969 + 3 ^ 40 * 3193456 * 2
def baseEnd_3193456 : Nat := 6748057106932357293883

theorem tailTrace_3193456 : CollatzResearch.WordTrace tailWord_3193456 prefixEnd_3193456 6748057106932357293883 := by
  unfold tailWord_3193456
  simp only [CollatzResearch.WordTrace]
  refine ⟨58237454559330892854244111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77649939412441190472325481 58237454559330892854244111)
  ·
    refine ⟨87356181838996339281366167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58237454559330892854244111 87356181838996339281366167)
    ·
      refine ⟨131034272758494508922049251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87356181838996339281366167 131034272758494508922049251)
      ·
        refine ⟨196551409137741763383073877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131034272758494508922049251 196551409137741763383073877)
        ·
          refine ⟨2303336825832911289645397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 196551409137741763383073877 2303336825832911289645397)
          ·
            refine ⟨6748057106932357293883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2303336825832911289645397 6748057106932357293883)
            ·
              rfl

theorem cell23_3193456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 10].length) (baseStart_3193456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193456 prefixEnd_3193456 := by exact prefixLift 3193456
  have htrace : WordTrace (prefixWord ++ tailWord_3193456) baseStart_3193456 baseEnd_3193456 := by
    simpa [prefixWord, tailWord_3193456, baseEnd_3193456] using wordTrace_append hprefix tailTrace_3193456
  have hstable : (prefixWord ++ tailWord_3193456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193456).length < 2 ^ (prefixWord ++ tailWord_3193456).sum := by decide
  have hdescent : baseEnd_3193456 < baseStart_3193456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_3193459 : Nat := 118140960795 + 3193459 * 2 ^ 59
def prefixEnd_3193459 : Nat := 4983230072969 + 3 ^ 40 * 3193459 * 2
def baseEnd_3193459 : Nat := 1639779417426526310676055

theorem tailTrace_3193459 : CollatzResearch.WordTrace tailWord_3193459 prefixEnd_3193459 1639779417426526310676055 := by
  unfold tailWord_3193459
  simp only [CollatzResearch.WordTrace]
  refine ⟨116475018537650917220847431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77650012358433944813898287 116475018537650917220847431)
  ·
    refine ⟨174712527806476375831271147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116475018537650917220847431 174712527806476375831271147)
    ·
      refine ⟨262068791709714563746906721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174712527806476375831271147 262068791709714563746906721)
      ·
        refine ⟨196551593782285922810180041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262068791709714563746906721 196551593782285922810180041)
        ·
          refine ⟨147413695336714442107635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196551593782285922810180041 147413695336714442107635031)
          ·
            refine ⟨221120543005071663161452547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147413695336714442107635031 221120543005071663161452547)
            ·
              refine ⟨331680814507607494742178821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221120543005071663161452547 331680814507607494742178821)
              ·
                refine ⟨62190152720176405264158529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331680814507607494742178821 62190152720176405264158529)
                ·
                  refine ⟨46642614540132303948118897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62190152720176405264158529 46642614540132303948118897)
                  ·
                    refine ⟨34981960905099227961089173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46642614540132303948118897 34981960905099227961089173)
                    ·
                      refine ⟨1639779417426526310676055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34981960905099227961089173 1639779417426526310676055)
                      ·
                        rfl

theorem cell23_3193459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_3193459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193459 prefixEnd_3193459 := by exact prefixLift 3193459
  have htrace : WordTrace (prefixWord ++ tailWord_3193459) baseStart_3193459 baseEnd_3193459 := by
    simpa [prefixWord, tailWord_3193459, baseEnd_3193459] using wordTrace_append hprefix tailTrace_3193459
  have hstable : (prefixWord ++ tailWord_3193459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193459).length < 2 ^ (prefixWord ++ tailWord_3193459).sum := by decide
  have hdescent : baseEnd_3193459 < baseStart_3193459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193461 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3193461 : Nat := 118140960795 + 3193461 * 2 ^ 59
def prefixEnd_3193461 : Nat := 4983230072969 + 3 ^ 40 * 3193461 * 2
def baseEnd_3193461 : Nat := 1639780444387835302851047

theorem tailTrace_3193461 : CollatzResearch.WordTrace tailWord_3193461 prefixEnd_3193461 1639780444387835302851047 := by
  unfold tailWord_3193461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116475091483643671562420237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77650060989095781041613491 116475091483643671562420237)
  ·
    refine ⟨43678159306366376835907589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116475091483643671562420237 43678159306366376835907589)
    ·
      refine ⟨8189654869943695656732673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43678159306366376835907589 8189654869943695656732673)
      ·
        refine ⟨6142241152457771742549505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8189654869943695656732673 6142241152457771742549505)
        ·
          refine ⟨4606680864343328806912129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6142241152457771742549505 4606680864343328806912129)
          ·
            refine ⟨3455010648257496605184097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606680864343328806912129 3455010648257496605184097)
            ·
              refine ⟨2591257986193122453888073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455010648257496605184097 2591257986193122453888073)
              ·
                refine ⟨1943443489644841840416055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591257986193122453888073 1943443489644841840416055)
                ·
                  refine ⟨2915165234467262760624083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943443489644841840416055 2915165234467262760624083)
                  ·
                    refine ⟨4372747851700894140936125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915165234467262760624083 4372747851700894140936125)
                    ·
                      refine ⟨1639780444387835302851047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4372747851700894140936125 1639780444387835302851047)
                      ·
                        rfl

theorem cell23_3193461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3193461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193461 prefixEnd_3193461 := by exact prefixLift 3193461
  have htrace : WordTrace (prefixWord ++ tailWord_3193461) baseStart_3193461 baseEnd_3193461 := by
    simpa [prefixWord, tailWord_3193461, baseEnd_3193461] using wordTrace_append hprefix tailTrace_3193461
  have hstable : (prefixWord ++ tailWord_3193461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193461).length < 2 ^ (prefixWord ++ tailWord_3193461).sum := by decide
  have hdescent : baseEnd_3193461 < baseStart_3193461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193486 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3193486 : Nat := 118140960795 + 3193486 * 2 ^ 59
def prefixEnd_3193486 : Nat := 4983230072969 + 3 ^ 40 * 3193486 * 2
def baseEnd_3193486 : Nat := 546597760468065901679477

theorem tailTrace_3193486 : CollatzResearch.WordTrace tailWord_3193486 prefixEnd_3193486 546597760468065901679477 := by
  unfold tailWord_3193486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559500413569137604010039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77650668872368733888053541 14559500413569137604010039)
  ·
    refine ⟨21839250620353706406015059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14559500413569137604010039 21839250620353706406015059)
    ·
      refine ⟨32758875930530559609022589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21839250620353706406015059 32758875930530559609022589)
      ·
        refine ⟨12284578473948959853383471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32758875930530559609022589 12284578473948959853383471)
        ·
          refine ⟨18426867710923439780075207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284578473948959853383471 18426867710923439780075207)
          ·
            refine ⟨27640301566385159670112811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18426867710923439780075207 27640301566385159670112811)
            ·
              refine ⟨41460452349577739505169217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27640301566385159670112811 41460452349577739505169217)
              ·
                refine ⟨31095339262183304628876913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41460452349577739505169217 31095339262183304628876913)
                ·
                  refine ⟨23321504446637478471657685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31095339262183304628876913 23321504446637478471657685)
                  ·
                    refine ⟨546597760468065901679477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23321504446637478471657685 546597760468065901679477)
                    ·
                      rfl

theorem cell23_3193486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3193486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193486 prefixEnd_3193486 := by exact prefixLift 3193486
  have htrace : WordTrace (prefixWord ++ tailWord_3193486) baseStart_3193486 baseEnd_3193486 := by
    simpa [prefixWord, tailWord_3193486, baseEnd_3193486] using wordTrace_append hprefix tailTrace_3193486
  have hstable : (prefixWord ++ tailWord_3193486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193486).length < 2 ^ (prefixWord ++ tailWord_3193486).sum := by decide
  have hdescent : baseEnd_3193486 < baseStart_3193486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193496 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3193496 : Nat := 118140960795 + 3193496 * 2 ^ 59
def prefixEnd_3193496 : Nat := 4983230072969 + 3 ^ 40 * 3193496 * 2
def baseEnd_3193496 : Nat := 1639798416210742665913385

theorem tailTrace_3193496 : CollatzResearch.WordTrace tailWord_3193496 prefixEnd_3193496 1639798416210742665913385 := by
  unfold tailWord_3193496
  simp only [CollatzResearch.WordTrace]
  refine ⟨58238184019258436269972171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77650912025677915026629561 58238184019258436269972171)
  ·
    refine ⟨87357276028887654404958257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58238184019258436269972171 87357276028887654404958257)
    ·
      refine ⟨65517957021665740803718693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87357276028887654404958257 65517957021665740803718693)
      ·
        refine ⟨12284616941562326400697255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65517957021665740803718693 12284616941562326400697255)
        ·
          refine ⟨18426925412343489601045883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284616941562326400697255 18426925412343489601045883)
          ·
            refine ⟨27640388118515234401568825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18426925412343489601045883 27640388118515234401568825)
            ·
              refine ⟨20730291088886425801176619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27640388118515234401568825 20730291088886425801176619)
              ·
                refine ⟨31095436633329638701764929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20730291088886425801176619 31095436633329638701764929)
                ·
                  refine ⟨23321577474997229026323697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31095436633329638701764929 23321577474997229026323697)
                  ·
                    refine ⟨17491183106247921769742773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23321577474997229026323697 17491183106247921769742773)
                    ·
                      refine ⟨1639798416210742665913385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17491183106247921769742773 1639798416210742665913385)
                      ·
                        rfl

theorem cell23_3193496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3193496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193496 prefixEnd_3193496 := by exact prefixLift 3193496
  have htrace : WordTrace (prefixWord ++ tailWord_3193496) baseStart_3193496 baseEnd_3193496 := by
    simpa [prefixWord, tailWord_3193496, baseEnd_3193496] using wordTrace_append hprefix tailTrace_3193496
  have hstable : (prefixWord ++ tailWord_3193496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193496).length < 2 ^ (prefixWord ++ tailWord_3193496).sum := by decide
  have hdescent : baseEnd_3193496 < baseStart_3193496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193504 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3]
def baseStart_3193504 : Nat := 118140960795 + 3193504 * 2 ^ 59
def prefixEnd_3193504 : Nat := 4983230072969 + 3 ^ 40 * 3193504 * 2
def baseEnd_3193504 : Nat := 1639802524055978634613349

theorem tailTrace_3193504 : CollatzResearch.WordTrace tailWord_3193504 prefixEnd_3193504 1639802524055978634613349 := by
  unfold tailWord_3193504
  simp only [CollatzResearch.WordTrace]
  refine ⟨58238329911243944953117783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77651106548325259937490377 58238329911243944953117783)
  ·
    refine ⟨87357494866865917429676675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58238329911243944953117783 87357494866865917429676675)
    ·
      refine ⟨131036242300298876144515013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87357494866865917429676675 131036242300298876144515013)
      ·
        refine ⟨24569295431306039277096565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131036242300298876144515013 24569295431306039277096565)
        ·
          refine ⟨2303371446684941182227803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24569295431306039277096565 2303371446684941182227803)
          ·
            refine ⟨3455057170027411773341705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303371446684941182227803 3455057170027411773341705)
            ·
              refine ⟨2591292877520558830006279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455057170027411773341705 2591292877520558830006279)
              ·
                refine ⟨3886939316280838245009419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591292877520558830006279 3886939316280838245009419)
                ·
                  refine ⟨5830408974421257367514129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886939316280838245009419 5830408974421257367514129)
                  ·
                    refine ⟨4372806730815943025635597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830408974421257367514129 4372806730815943025635597)
                    ·
                      refine ⟨1639802524055978634613349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4372806730815943025635597 1639802524055978634613349)
                      ·
                        rfl

theorem cell23_3193504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_3193504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193504 prefixEnd_3193504 := by exact prefixLift 3193504
  have htrace : WordTrace (prefixWord ++ tailWord_3193504) baseStart_3193504 baseEnd_3193504 := by
    simpa [prefixWord, tailWord_3193504, baseEnd_3193504] using wordTrace_append hprefix tailTrace_3193504
  have hstable : (prefixWord ++ tailWord_3193504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193504).length < 2 ^ (prefixWord ++ tailWord_3193504).sum := by decide
  have hdescent : baseEnd_3193504 < baseStart_3193504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193517 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3193517 : Nat := 118140960795 + 3193517 * 2 ^ 59
def prefixEnd_3193517 : Nat := 4983230072969 + 3 ^ 40 * 3193517 * 2
def baseEnd_3193517 : Nat := 1639809199304487083750789

theorem tailTrace_3193517 : CollatzResearch.WordTrace tailWord_3193517 prefixEnd_3193517 1639809199304487083750789 := by
  unfold tailWord_3193517
  simp only [CollatzResearch.WordTrace]
  refine ⟨116477133971440793126458805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77651422647627195417639203 116477133971440793126458805)
  ·
    refine ⟨10919731309822574355605513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116477133971440793126458805 10919731309822574355605513)
    ·
      refine ⟨8189798482366930766704135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10919731309822574355605513 8189798482366930766704135)
      ·
        refine ⟨12284697723550396150056203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8189798482366930766704135 12284697723550396150056203)
        ·
          refine ⟨18427046585325594225084305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284697723550396150056203 18427046585325594225084305)
          ·
            refine ⟨13820284938994195668813229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18427046585325594225084305 13820284938994195668813229)
            ·
              refine ⟨5182606852122823375804961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13820284938994195668813229 5182606852122823375804961)
              ·
                refine ⟨3886955139092117531853721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182606852122823375804961 3886955139092117531853721)
                ·
                  refine ⟨2915216354319088148890291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886955139092117531853721 2915216354319088148890291)
                  ·
                    refine ⟨4372824531478632223335437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915216354319088148890291 4372824531478632223335437)
                    ·
                      refine ⟨1639809199304487083750789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4372824531478632223335437 1639809199304487083750789)
                      ·
                        rfl

theorem cell23_3193517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3193517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193517 prefixEnd_3193517 := by exact prefixLift 3193517
  have htrace : WordTrace (prefixWord ++ tailWord_3193517) baseStart_3193517 baseEnd_3193517 := by
    simpa [prefixWord, tailWord_3193517, baseEnd_3193517] using wordTrace_append hprefix tailTrace_3193517
  have hstable : (prefixWord ++ tailWord_3193517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193517).length < 2 ^ (prefixWord ++ tailWord_3193517).sum := by decide
  have hdescent : baseEnd_3193517 < baseStart_3193517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193640 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3193640 : Nat := 118140960795 + 3193640 * 2 ^ 59
def prefixEnd_3193640 : Nat := 4983230072969 + 3 ^ 40 * 3193640 * 2
def baseEnd_3193640 : Nat := 546624119141663367504241

theorem tailTrace_3193640 : CollatzResearch.WordTrace tailWord_3193640 prefixEnd_3193640 546624119141663367504241 := by
  unfold tailWord_3193640
  simp only [CollatzResearch.WordTrace]
  refine ⟨58240810074997592566593187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77654413433330123422124249 58240810074997592566593187)
  ·
    refine ⟨87361215112496388849889781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58240810074997592566593187 87361215112496388849889781)
    ·
      refine ⟨8190113916796536454677167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87361215112496388849889781 8190113916796536454677167)
      ·
        refine ⟨12285170875194804682015751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8190113916796536454677167 12285170875194804682015751)
        ·
          refine ⟨18427756312792207023023627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285170875194804682015751 18427756312792207023023627)
          ·
            refine ⟨27641634469188310534535441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18427756312792207023023627 27641634469188310534535441)
            ·
              refine ⟨20731225851891232900901581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27641634469188310534535441 20731225851891232900901581)
              ·
                refine ⟨7774209694459212337838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20731225851891232900901581 7774209694459212337838093)
                ·
                  refine ⟨2915328635422204626689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7774209694459212337838093 2915328635422204626689285)
                  ·
                    refine ⟨546624119141663367504241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915328635422204626689285 546624119141663367504241)
                    ·
                      rfl

theorem cell23_3193640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3193640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193640 prefixEnd_3193640 := by exact prefixLift 3193640
  have htrace : WordTrace (prefixWord ++ tailWord_3193640) baseStart_3193640 baseEnd_3193640 := by
    simpa [prefixWord, tailWord_3193640, baseEnd_3193640] using wordTrace_append hprefix tailTrace_3193640
  have hstable : (prefixWord ++ tailWord_3193640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193640).length < 2 ^ (prefixWord ++ tailWord_3193640).sum := by decide
  have hdescent : baseEnd_3193640 < baseStart_3193640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193717 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3193717 : Nat := 118140960795 + 3193717 * 2 ^ 59
def prefixEnd_3193717 : Nat := 4983230072969 + 3 ^ 40 * 3193717 * 2
def baseEnd_3193717 : Nat := 546637298478462100416623

theorem tailTrace_3193717 : CollatzResearch.WordTrace tailWord_3193717 prefixEnd_3193717 546637298478462100416623 := by
  unfold tailWord_3193717
  simp only [CollatzResearch.WordTrace]
  refine ⟨116484428570716227283739405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77656285713810818189159603 116484428570716227283739405)
  ·
    refine ⟨43681660714018585231402277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116484428570716227283739405 43681660714018585231402277)
    ·
      refine ⟨8190311383878484730887927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43681660714018585231402277 8190311383878484730887927)
      ·
        refine ⟨12285467075817727096331891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8190311383878484730887927 12285467075817727096331891)
        ·
          refine ⟨18428200613726590644497837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285467075817727096331891 18428200613726590644497837)
          ·
            refine ⟨6910575230147471491686689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18428200613726590644497837 6910575230147471491686689)
            ·
              refine ⟨5182931422610603618765017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910575230147471491686689 5182931422610603618765017)
              ·
                refine ⟨3887198566957952714073763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182931422610603618765017 3887198566957952714073763)
                ·
                  refine ⟨5830797850436929071110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887198566957952714073763 5830797850436929071110645)
                  ·
                    refine ⟨546637298478462100416623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5830797850436929071110645 546637298478462100416623)
                    ·
                      rfl

theorem cell23_3193717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3193717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193717 prefixEnd_3193717 := by exact prefixLift 3193717
  have htrace : WordTrace (prefixWord ++ tailWord_3193717) baseStart_3193717 baseEnd_3193717 := by
    simpa [prefixWord, tailWord_3193717, baseEnd_3193717] using wordTrace_append hprefix tailTrace_3193717
  have hstable : (prefixWord ++ tailWord_3193717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193717).length < 2 ^ (prefixWord ++ tailWord_3193717).sum := by decide
  have hdescent : baseEnd_3193717 < baseStart_3193717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193783 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3193783 : Nat := 118140960795 + 3193783 * 2 ^ 59
def prefixEnd_3193783 : Nat := 4983230072969 + 3 ^ 40 * 3193783 * 2
def baseEnd_3193783 : Nat := 1639945785158583043024565

theorem tailTrace_3193783 : CollatzResearch.WordTrace tailWord_3193783 prefixEnd_3193783 1639945785158583043024565 := by
  unfold tailWord_3193783
  simp only [CollatzResearch.WordTrace]
  refine ⟨116486835788477120555642003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77657890525651413703761335 116486835788477120555642003)
  ·
    refine ⟨174730253682715680833463005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116486835788477120555642003 174730253682715680833463005)
    ·
      refine ⟨65523845131018380312548627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174730253682715680833463005 65523845131018380312548627)
      ·
        refine ⟨98285767696527570468822941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65523845131018380312548627 98285767696527570468822941)
        ·
          refine ⟨36857162886197838925808603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98285767696527570468822941 36857162886197838925808603)
          ·
            refine ⟨55285744329296758388712905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36857162886197838925808603 55285744329296758388712905)
            ·
              refine ⟨41464308246972568791534679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55285744329296758388712905 41464308246972568791534679)
              ·
                refine ⟨62196462370458853187302019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41464308246972568791534679 62196462370458853187302019)
                ·
                  refine ⟨93294693555688279780953029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62196462370458853187302019 93294693555688279780953029)
                  ·
                    refine ⟨17492755041691552458928693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93294693555688279780953029 17492755041691552458928693)
                    ·
                      refine ⟨1639945785158583043024565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17492755041691552458928693 1639945785158583043024565)
                      ·
                        rfl

theorem cell23_3193783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3193783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193783 prefixEnd_3193783 := by exact prefixLift 3193783
  have htrace : WordTrace (prefixWord ++ tailWord_3193783) baseStart_3193783 baseEnd_3193783 := by
    simpa [prefixWord, tailWord_3193783, baseEnd_3193783] using wordTrace_append hprefix tailTrace_3193783
  have hstable : (prefixWord ++ tailWord_3193783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193783).length < 2 ^ (prefixWord ++ tailWord_3193783).sum := by decide
  have hdescent : baseEnd_3193783 < baseStart_3193783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193804 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3193804 : Nat := 118140960795 + 3193804 * 2 ^ 59
def prefixEnd_3193804 : Nat := 4983230072969 + 3 ^ 40 * 3193804 * 2
def baseEnd_3193804 : Nat := 1639956568252327460861969

theorem tailTrace_3193804 : CollatzResearch.WordTrace tailWord_3193804 prefixEnd_3193804 1639956568252327460861969 := by
  unfold tailWord_3193804
  simp only [CollatzResearch.WordTrace]
  refine ⟨58243800860700520571078233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77658401147600694094770977 58243800860700520571078233)
  ·
    refine ⟨43682850645525390428308675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58243800860700520571078233 43682850645525390428308675)
    ·
      refine ⟨65524275968288085642463013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43682850645525390428308675 65524275968288085642463013)
      ·
        refine ⟨12285801744054016057961815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65524275968288085642463013 12285801744054016057961815)
        ·
          refine ⟨18428702616081024086942723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285801744054016057961815 18428702616081024086942723)
          ·
            refine ⟨27643053924121536130414085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18428702616081024086942723 27643053924121536130414085)
            ·
              refine ⟨5183072610772788024452641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27643053924121536130414085 5183072610772788024452641)
              ·
                refine ⟨3887304458079591018339481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183072610772788024452641 3887304458079591018339481)
                ·
                  refine ⟨2915478343559693263754611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887304458079591018339481 2915478343559693263754611)
                  ·
                    refine ⟨4373217515339539895631917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915478343559693263754611 4373217515339539895631917)
                    ·
                      refine ⟨1639956568252327460861969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373217515339539895631917 1639956568252327460861969)
                      ·
                        rfl

theorem cell23_3193804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3193804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193804 prefixEnd_3193804 := by exact prefixLift 3193804
  have htrace : WordTrace (prefixWord ++ tailWord_3193804) baseStart_3193804 baseEnd_3193804 := by
    simpa [prefixWord, tailWord_3193804, baseEnd_3193804] using wordTrace_append hprefix tailTrace_3193804
  have hstable : (prefixWord ++ tailWord_3193804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193804).length < 2 ^ (prefixWord ++ tailWord_3193804).sum := by decide
  have hdescent : baseEnd_3193804 < baseStart_3193804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193843 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_3193843 : Nat := 118140960795 + 3193843 * 2 ^ 59
def prefixEnd_3193843 : Nat := 4983230072969 + 3 ^ 40 * 3193843 * 2
def baseEnd_3193843 : Nat := 1639976593997852808274289

theorem tailTrace_3193843 : CollatzResearch.WordTrace tailWord_3193843 prefixEnd_3193843 1639976593997852808274289 := by
  unfold tailWord_3193843
  simp only [CollatzResearch.WordTrace]
  refine ⟨116489024168259750802826183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77659349445506500535217455 116489024168259750802826183)
  ·
    refine ⟨174733536252389626204239275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116489024168259750802826183 174733536252389626204239275)
    ·
      refine ⟨262100304378584439306358913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174733536252389626204239275 262100304378584439306358913)
      ·
        refine ⟨196575228283938329479769185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262100304378584439306358913 196575228283938329479769185)
        ·
          refine ⟨147431421212953747109826889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196575228283938329479769185 147431421212953747109826889)
          ·
            refine ⟨110573565909715310332370167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147431421212953747109826889 110573565909715310332370167)
            ·
              refine ⟨165860348864572965498555251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110573565909715310332370167 165860348864572965498555251)
              ·
                refine ⟨248790523296859448247832877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165860348864572965498555251 248790523296859448247832877)
                ·
                  refine ⟨93296446236322293092937329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248790523296859448247832877 93296446236322293092937329)
                  ·
                    refine ⟨69972334677241719819702997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93296446236322293092937329 69972334677241719819702997)
                    ·
                      refine ⟨1639976593997852808274289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69972334677241719819702997 1639976593997852808274289)
                      ·
                        rfl

theorem cell23_3193843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_3193843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193843 prefixEnd_3193843 := by exact prefixLift 3193843
  have htrace : WordTrace (prefixWord ++ tailWord_3193843) baseStart_3193843 baseEnd_3193843 := by
    simpa [prefixWord, tailWord_3193843, baseEnd_3193843] using wordTrace_append hprefix tailTrace_3193843
  have hstable : (prefixWord ++ tailWord_3193843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193843).length < 2 ^ (prefixWord ++ tailWord_3193843).sum := by decide
  have hdescent : baseEnd_3193843 < baseStart_3193843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193867 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 5]
def baseStart_3193867 : Nat := 118140960795 + 3193867 * 2 ^ 59
def prefixEnd_3193867 : Nat := 4983230072969 + 3 ^ 40 * 3193867 * 2
def baseEnd_3193867 : Nat := 182220990837062301597131

theorem tailTrace_3193867 : CollatzResearch.WordTrace tailWord_3193867 prefixEnd_3193867 182220990837062301597131 := by
  unfold tailWord_3193867
  simp only [CollatzResearch.WordTrace]
  refine ⟨116489899520172802901699855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77659933013448535267799903 116489899520172802901699855)
  ·
    refine ⟨174734849280259204352549783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116489899520172802901699855 174734849280259204352549783)
    ·
      refine ⟨262102273920388806528824675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174734849280259204352549783 262102273920388806528824675)
      ·
        refine ⟨393153410880583209793237013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262102273920388806528824675 393153410880583209793237013)
        ·
          refine ⟨18429066135027337959057985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 393153410880583209793237013 18429066135027337959057985)
          ·
            refine ⟨13821799601270503469293489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18429066135027337959057985 13821799601270503469293489)
            ·
              refine ⟨10366349700952877601970117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13821799601270503469293489 10366349700952877601970117)
              ·
                refine ⟨1943690568928664550369397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10366349700952877601970117 1943690568928664550369397)
                ·
                  refine ⟨182220990837062301597131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943690568928664550369397 182220990837062301597131)
                  ·
                    rfl

theorem cell23_3193867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 5].length) (baseStart_3193867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193867 prefixEnd_3193867 := by exact prefixLift 3193867
  have htrace : WordTrace (prefixWord ++ tailWord_3193867) baseStart_3193867 baseEnd_3193867 := by
    simpa [prefixWord, tailWord_3193867, baseEnd_3193867] using wordTrace_append hprefix tailTrace_3193867
  have hstable : (prefixWord ++ tailWord_3193867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193867).length < 2 ^ (prefixWord ++ tailWord_3193867).sum := by decide
  have hdescent : baseEnd_3193867 < baseStart_3193867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193877 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_3193877 : Nat := 118140960795 + 3193877 * 2 ^ 59
def prefixEnd_3193877 : Nat := 4983230072969 + 3 ^ 40 * 3193877 * 2
def baseEnd_3193877 : Nat := 1639994052340105675249133

theorem tailTrace_3193877 : CollatzResearch.WordTrace tailWord_3193877 prefixEnd_3193877 1639994052340105675249133 := by
  unfold tailWord_3193877
  simp only [CollatzResearch.WordTrace]
  refine ⟨116490264250136574609563885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77660176166757716406375923 116490264250136574609563885)
  ·
    refine ⟨43683849093801215478586457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116490264250136574609563885 43683849093801215478586457)
    ·
      refine ⟨32762886820350911608939843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43683849093801215478586457 32762886820350911608939843)
      ·
        refine ⟨49144330230526367413409765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32762886820350911608939843 49144330230526367413409765)
        ·
          refine ⟨9214561918223693890014331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49144330230526367413409765 9214561918223693890014331)
          ·
            refine ⟨13821842877335540835021497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214561918223693890014331 13821842877335540835021497)
            ·
              refine ⟨10366382158001655626266123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13821842877335540835021497 10366382158001655626266123)
              ·
                refine ⟨15549573237002483439399185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366382158001655626266123 15549573237002483439399185)
                ·
                  refine ⟨11662179927751862579549389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15549573237002483439399185 11662179927751862579549389)
                  ·
                    refine ⟨4373317472906948467331021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11662179927751862579549389 4373317472906948467331021)
                    ·
                      refine ⟨1639994052340105675249133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373317472906948467331021 1639994052340105675249133)
                      ·
                        rfl

theorem cell23_3193877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_3193877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193877 prefixEnd_3193877 := by exact prefixLift 3193877
  have htrace : WordTrace (prefixWord ++ tailWord_3193877) baseStart_3193877 baseEnd_3193877 := by
    simpa [prefixWord, tailWord_3193877, baseEnd_3193877] using wordTrace_append hprefix tailTrace_3193877
  have hstable : (prefixWord ++ tailWord_3193877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193877).length < 2 ^ (prefixWord ++ tailWord_3193877).sum := by decide
  have hdescent : baseEnd_3193877 < baseStart_3193877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193880 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_3193880 : Nat := 118140960795 + 3193880 * 2 ^ 59
def prefixEnd_3193880 : Nat := 4983230072969 + 3 ^ 40 * 3193880 * 2
def baseEnd_3193880 : Nat := 546665197594023054503873

theorem tailTrace_3193880 : CollatzResearch.WordTrace tailWord_3193880 prefixEnd_3193880 546665197594023054503873 := by
  unfold tailWord_3193880
  simp only [CollatzResearch.WordTrace]
  refine ⟨58245186834562853060961547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77660249112750470747948729 58245186834562853060961547)
  ·
    refine ⟨87367780251844279591442321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58245186834562853060961547 87367780251844279591442321)
    ·
      refine ⟨65525835188883209693581741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87367780251844279591442321 65525835188883209693581741)
      ·
        refine ⟨24572188195831203635093153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65525835188883209693581741 24572188195831203635093153)
        ·
          refine ⟨18429141146873402726319865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24572188195831203635093153 18429141146873402726319865)
          ·
            refine ⟨13821855860155052044739899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18429141146873402726319865 13821855860155052044739899)
            ·
              refine ⟨20732783790232578067109849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13821855860155052044739899 20732783790232578067109849)
              ·
                refine ⟨15549587842674433550332387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20732783790232578067109849 15549587842674433550332387)
                ·
                  refine ⟨23324381764011650325498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15549587842674433550332387 23324381764011650325498581)
                  ·
                    refine ⟨546665197594023054503873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23324381764011650325498581 546665197594023054503873)
                    ·
                      rfl

theorem cell23_3193880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_3193880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193880 prefixEnd_3193880 := by exact prefixLift 3193880
  have htrace : WordTrace (prefixWord ++ tailWord_3193880) baseStart_3193880 baseEnd_3193880 := by
    simpa [prefixWord, tailWord_3193880, baseEnd_3193880] using wordTrace_append hprefix tailTrace_3193880
  have hstable : (prefixWord ++ tailWord_3193880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193880).length < 2 ^ (prefixWord ++ tailWord_3193880).sum := by decide
  have hdescent : baseEnd_3193880 < baseStart_3193880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193900 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3193900 : Nat := 118140960795 + 3193900 * 2 ^ 59
def prefixEnd_3193900 : Nat := 4983230072969 + 3 ^ 40 * 3193900 * 2
def baseEnd_3193900 : Nat := 1640005862395159085261527

theorem tailTrace_3193900 : CollatzResearch.WordTrace tailWord_3193900 prefixEnd_3193900 1640005862395159085261527 := by
  unfold tailWord_3193900
  simp only [CollatzResearch.WordTrace]
  refine ⟨58245551564526624768825577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77660735419368833025100769 58245551564526624768825577)
  ·
    refine ⟨43684163673394968576619183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58245551564526624768825577 43684163673394968576619183)
    ·
      refine ⟨65526245510092452864928775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43684163673394968576619183 65526245510092452864928775)
      ·
        refine ⟨98289368265138679297393163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65526245510092452864928775 98289368265138679297393163)
        ·
          refine ⟨147434052397708018946089745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98289368265138679297393163 147434052397708018946089745)
          ·
            refine ⟨110575539298281014209567309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147434052397708018946089745 110575539298281014209567309)
            ·
              refine ⟨41465827236855380328587741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110575539298281014209567309 41465827236855380328587741)
              ·
                refine ⟨15549685213820767623220403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41465827236855380328587741 15549685213820767623220403)
                ·
                  refine ⟨23324527820731151434830605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15549685213820767623220403 23324527820731151434830605)
                  ·
                    refine ⟨8746697932774181788061477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23324527820731151434830605 8746697932774181788061477)
                    ·
                      refine ⟨1640005862395159085261527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8746697932774181788061477 1640005862395159085261527)
                      ·
                        rfl

theorem cell23_3193900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3193900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193900 prefixEnd_3193900 := by exact prefixLift 3193900
  have htrace : WordTrace (prefixWord ++ tailWord_3193900) baseStart_3193900 baseEnd_3193900 := by
    simpa [prefixWord, tailWord_3193900, baseEnd_3193900] using wordTrace_append hprefix tailTrace_3193900
  have hstable : (prefixWord ++ tailWord_3193900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193900).length < 2 ^ (prefixWord ++ tailWord_3193900).sum := by decide
  have hdescent : baseEnd_3193900 < baseStart_3193900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193917 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3193917 : Nat := 118140960795 + 3193917 * 2 ^ 59
def prefixEnd_3193917 : Nat := 4983230072969 + 3 ^ 40 * 3193917 * 2
def baseEnd_3193917 : Nat := 1640014591566285518748949

theorem tailTrace_3193917 : CollatzResearch.WordTrace tailWord_3193917 prefixEnd_3193917 1640014591566285518748949 := by
  unfold tailWord_3193917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116491723169991661441020005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77661148779994440960680003 116491723169991661441020005)
  ·
    refine ⟨21842198094373436520191251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116491723169991661441020005 21842198094373436520191251)
    ·
      refine ⟨32763297141560154780286877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21842198094373436520191251 32763297141560154780286877)
      ·
        refine ⟨12286236428085058042607579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32763297141560154780286877 12286236428085058042607579)
        ·
          refine ⟨18429354642127587063911369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286236428085058042607579 18429354642127587063911369)
          ·
            refine ⟨13822015981595690297933527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18429354642127587063911369 13822015981595690297933527)
            ·
              refine ⟨20733023972393535446900291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822015981595690297933527 20733023972393535446900291)
              ·
                refine ⟨31099535958590303170350437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20733023972393535446900291 31099535958590303170350437)
                ·
                  refine ⟨5831162992235681844440707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31099535958590303170350437 5831162992235681844440707)
                  ·
                    refine ⟨8746744488353522766661061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831162992235681844440707 8746744488353522766661061)
                    ·
                      refine ⟨1640014591566285518748949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8746744488353522766661061 1640014591566285518748949)
                      ·
                        rfl

theorem cell23_3193917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3193917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193917 prefixEnd_3193917 := by exact prefixLift 3193917
  have htrace : WordTrace (prefixWord ++ tailWord_3193917) baseStart_3193917 baseEnd_3193917 := by
    simpa [prefixWord, tailWord_3193917, baseEnd_3193917] using wordTrace_append hprefix tailTrace_3193917
  have hstable : (prefixWord ++ tailWord_3193917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193917).length < 2 ^ (prefixWord ++ tailWord_3193917).sum := by decide
  have hdescent : baseEnd_3193917 < baseStart_3193917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193930 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3193930 : Nat := 118140960795 + 3193930 * 2 ^ 59
def prefixEnd_3193930 : Nat := 4983230072969 + 3 ^ 40 * 3193930 * 2
def baseEnd_3193930 : Nat := 1640021266814793967886389

theorem tailTrace_3193930 : CollatzResearch.WordTrace tailWord_3193930 prefixEnd_3193930 1640021266814793967886389 := by
  unfold tailWord_3193930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123049329736141165310811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77661464879296376440828829 29123049329736141165310811)
  ·
    refine ⟨43684573994604211747966217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29123049329736141165310811 43684573994604211747966217)
    ·
      refine ⟨32763430495953158810974663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43684573994604211747966217 32763430495953158810974663)
      ·
        refine ⟨49145145743929738216461995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32763430495953158810974663 49145145743929738216461995)
        ·
          refine ⟨73717718615894607324692993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49145145743929738216461995 73717718615894607324692993)
          ·
            refine ⟨55288288961920955493519745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73717718615894607324692993 55288288961920955493519745)
            ·
              refine ⟨41466216721440716620139809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55288288961920955493519745 41466216721440716620139809)
              ·
                refine ⟨31099662541080537465104857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41466216721440716620139809 31099662541080537465104857)
                ·
                  refine ⟨23324746905810403098828643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31099662541080537465104857 23324746905810403098828643)
                  ·
                    refine ⟨34987120358715604648242965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23324746905810403098828643 34987120358715604648242965)
                    ·
                      refine ⟨1640021266814793967886389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34987120358715604648242965 1640021266814793967886389)
                      ·
                        rfl

theorem cell23_3193930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3193930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193930 prefixEnd_3193930 := by exact prefixLift 3193930
  have htrace : WordTrace (prefixWord ++ tailWord_3193930) baseStart_3193930 baseEnd_3193930 := by
    simpa [prefixWord, tailWord_3193930, baseEnd_3193930] using wordTrace_append hprefix tailTrace_3193930
  have hstable : (prefixWord ++ tailWord_3193930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193930).length < 2 ^ (prefixWord ++ tailWord_3193930).sum := by decide
  have hdescent : baseEnd_3193930 < baseStart_3193930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193974 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3193974 : Nat := 118140960795 + 3193974 * 2 ^ 59
def prefixEnd_3193974 : Nat := 4983230072969 + 3 ^ 40 * 3193974 * 2
def baseEnd_3193974 : Nat := 182227095551510199526243

theorem tailTrace_3193974 : CollatzResearch.WordTrace tailWord_3193974 prefixEnd_3193974 182227095551510199526243 := by
  unfold tailWord_3193974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280862633174072510990311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77662534753856773450563317 7280862633174072510990311)
  ·
    refine ⟨10921293949761108766485467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280862633174072510990311 10921293949761108766485467)
    ·
      refine ⟨16381940924641663149728201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921293949761108766485467 16381940924641663149728201)
      ·
        refine ⟨12286455693481247362296151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16381940924641663149728201 12286455693481247362296151)
        ·
          refine ⟨18429683540221871043444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286455693481247362296151 18429683540221871043444227)
          ·
            refine ⟨27644525310332806565166341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18429683540221871043444227 27644525310332806565166341)
            ·
              refine ⟨5183348495687401230968689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27644525310332806565166341 5183348495687401230968689)
              ·
                refine ⟨3887511371765550923226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183348495687401230968689 3887511371765550923226517)
                ·
                  refine ⟨182227095551510199526243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3887511371765550923226517 182227095551510199526243)
                  ·
                    rfl

theorem cell23_3193974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3193974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193974 prefixEnd_3193974 := by exact prefixLift 3193974
  have htrace : WordTrace (prefixWord ++ tailWord_3193974) baseStart_3193974 baseEnd_3193974 := by
    simpa [prefixWord, tailWord_3193974, baseEnd_3193974] using wordTrace_append hprefix tailTrace_3193974
  have hstable : (prefixWord ++ tailWord_3193974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193974).length < 2 ^ (prefixWord ++ tailWord_3193974).sum := by decide
  have hdescent : baseEnd_3193974 < baseStart_3193974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193994 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3193994 : Nat := 118140960795 + 3193994 * 2 ^ 59
def prefixEnd_3193994 : Nat := 4983230072969 + 3 ^ 40 * 3193994 * 2
def baseEnd_3193994 : Nat := 1640054129576681717486095

theorem tailTrace_3193994 : CollatzResearch.WordTrace tailWord_3193994 prefixEnd_3193994 1640054129576681717486095 := by
  unfold tailWord_3193994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123632897678175897893259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77663021060475135727715357 29123632897678175897893259)
  ·
    refine ⟨43685449346517263846839889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29123632897678175897893259 43685449346517263846839889)
    ·
      refine ⟨32764087009887947885129917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43685449346517263846839889 32764087009887947885129917)
      ·
        refine ⟨12286532628707980456923719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32764087009887947885129917 12286532628707980456923719)
        ·
          refine ⟨18429798943061970685385579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286532628707980456923719 18429798943061970685385579)
          ·
            refine ⟨27644698414592956028078369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18429798943061970685385579 27644698414592956028078369)
            ·
              refine ⟨20733523810944717021058777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27644698414592956028078369 20733523810944717021058777)
              ·
                refine ⟨15550142858208537765794083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20733523810944717021058777 15550142858208537765794083)
                ·
                  refine ⟨23325214287312806648691125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15550142858208537765794083 23325214287312806648691125)
                  ·
                    refine ⟨2186738839435575623314793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23325214287312806648691125 2186738839435575623314793)
                    ·
                      refine ⟨1640054129576681717486095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186738839435575623314793 1640054129576681717486095)
                      ·
                        rfl

theorem cell23_3193994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3193994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3193994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3193994 prefixEnd_3193994 := by exact prefixLift 3193994
  have htrace : WordTrace (prefixWord ++ tailWord_3193994) baseStart_3193994 baseEnd_3193994 := by
    simpa [prefixWord, tailWord_3193994, baseEnd_3193994] using wordTrace_append hprefix tailTrace_3193994
  have hstable : (prefixWord ++ tailWord_3193994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193994).length < 2 ^ (prefixWord ++ tailWord_3193994).sum := by decide
  have hdescent : baseEnd_3193994 < baseStart_3193994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194017 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3194017 : Nat := 118140960795 + 3194017 * 2 ^ 59
def prefixEnd_3194017 : Nat := 4983230072969 + 3 ^ 40 * 3194017 * 2
def baseEnd_3194017 : Nat := 546688646543911709166163

theorem tailTrace_3194017 : CollatzResearch.WordTrace tailWord_3194017 prefixEnd_3194017 546688646543911709166163 := by
  unfold tailWord_3194017
  simp only [CollatzResearch.WordTrace]
  refine ⟨116495370469629378519660305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77663580313086252346440203 116495370469629378519660305)
  ·
    refine ⟨87371527852222033889745229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116495370469629378519660305 87371527852222033889745229)
    ·
      refine ⟨32764322944583262708654461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87371527852222033889745229 32764322944583262708654461)
      ·
        refine ⟨12286621104218723515745423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32764322944583262708654461 12286621104218723515745423)
        ·
          refine ⟨18429931656328085273618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286621104218723515745423 18429931656328085273618135)
          ·
            refine ⟨27644897484492127910427203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18429931656328085273618135 27644897484492127910427203)
            ·
              refine ⟨41467346226738191865640805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27644897484492127910427203 41467346226738191865640805)
              ·
                refine ⟨7775127417513410974807651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41467346226738191865640805 7775127417513410974807651)
                ·
                  refine ⟨11662691126270116462211477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7775127417513410974807651 11662691126270116462211477)
                  ·
                    refine ⟨546688646543911709166163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11662691126270116462211477 546688646543911709166163)
                    ·
                      rfl

theorem cell23_3194017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3194017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194017 prefixEnd_3194017 := by exact prefixLift 3194017
  have htrace : WordTrace (prefixWord ++ tailWord_3194017) baseStart_3194017 baseEnd_3194017 := by
    simpa [prefixWord, tailWord_3194017, baseEnd_3194017] using wordTrace_append hprefix tailTrace_3194017
  have hstable : (prefixWord ++ tailWord_3194017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194017).length < 2 ^ (prefixWord ++ tailWord_3194017).sum := by decide
  have hdescent : baseEnd_3194017 < baseStart_3194017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194021 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_3194021 : Nat := 118140960795 + 3194021 * 2 ^ 59
def prefixEnd_3194021 : Nat := 4983230072969 + 3 ^ 40 * 3194021 * 2
def baseEnd_3194021 : Nat := 546689331184784370616157

theorem tailTrace_3194021 : CollatzResearch.WordTrace tailWord_3194021 prefixEnd_3194021 546689331184784370616157 := by
  unfold tailWord_3194021
  simp only [CollatzResearch.WordTrace]
  refine ⟨116495516361614887202805917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77663677574409924801870611 116495516361614887202805917)
  ·
    refine ⟨43685818635605582701052219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116495516361614887202805917 43685818635605582701052219)
    ·
      refine ⟨65528727953408374051578329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43685818635605582701052219 65528727953408374051578329)
      ·
        refine ⟨49146545965056280538683747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65528727953408374051578329 49146545965056280538683747)
        ·
          refine ⟨73719818947584420808025621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49146545965056280538683747 73719818947584420808025621)
          ·
            refine ⟨3455616513168019725376201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73719818947584420808025621 3455616513168019725376201)
            ·
              refine ⟨2591712384876014794032151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455616513168019725376201 2591712384876014794032151)
              ·
                refine ⟨3887568577314022191048227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591712384876014794032151 3887568577314022191048227)
                ·
                  refine ⟨5831352865971033286572341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887568577314022191048227 5831352865971033286572341)
                  ·
                    refine ⟨546689331184784370616157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831352865971033286572341 546689331184784370616157)
                    ·
                      rfl

theorem cell23_3194021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_3194021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194021 prefixEnd_3194021 := by exact prefixLift 3194021
  have htrace : WordTrace (prefixWord ++ tailWord_3194021) baseStart_3194021 baseEnd_3194021 := by
    simpa [prefixWord, tailWord_3194021, baseEnd_3194021] using wordTrace_append hprefix tailTrace_3194021
  have hstable : (prefixWord ++ tailWord_3194021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194021).length < 2 ^ (prefixWord ++ tailWord_3194021).sum := by decide
  have hdescent : baseEnd_3194021 < baseStart_3194021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194034 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3194034 : Nat := 118140960795 + 3194034 * 2 ^ 59
def prefixEnd_3194034 : Nat := 4983230072969 + 3 ^ 40 * 3194034 * 2
def baseEnd_3194034 : Nat := 546691556267620520328637

theorem tailTrace_3194034 : CollatzResearch.WordTrace tailWord_3194034 prefixEnd_3194034 546691556267620520328637 := by
  unfold tailWord_3194034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123997627641947605757289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77663993673711860282019437 29123997627641947605757289)
  ·
    refine ⟨21842998220731460704317967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29123997627641947605757289 21842998220731460704317967)
    ·
      refine ⟨32764497331097191056476951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21842998220731460704317967 32764497331097191056476951)
      ·
        refine ⟨49146745996645786584715427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32764497331097191056476951 49146745996645786584715427)
        ·
          refine ⟨73720118994968679877073141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49146745996645786584715427 73720118994968679877073141)
          ·
            refine ⟨6911261155778313738475607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73720118994968679877073141 6911261155778313738475607)
            ·
              refine ⟨10366891733667470607713411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911261155778313738475607 10366891733667470607713411)
              ·
                refine ⟨15550337600501205911570117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366891733667470607713411 15550337600501205911570117)
                ·
                  refine ⟨2915688300093976108419397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15550337600501205911570117 2915688300093976108419397)
                  ·
                    refine ⟨546691556267620520328637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915688300093976108419397 546691556267620520328637)
                    ·
                      rfl

theorem cell23_3194034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3194034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194034 prefixEnd_3194034 := by exact prefixLift 3194034
  have htrace : WordTrace (prefixWord ++ tailWord_3194034) baseStart_3194034 baseEnd_3194034 := by
    simpa [prefixWord, tailWord_3194034, baseEnd_3194034] using wordTrace_append hprefix tailTrace_3194034
  have hstable : (prefixWord ++ tailWord_3194034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194034).length < 2 ^ (prefixWord ++ tailWord_3194034).sum := by decide
  have hdescent : baseEnd_3194034 < baseStart_3194034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194041 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3194041 : Nat := 118140960795 + 3194041 * 2 ^ 59
def prefixEnd_3194041 : Nat := 4983230072969 + 3 ^ 40 * 3194041 * 2
def baseEnd_3194041 : Nat := 1640078263167443033598379

theorem tailTrace_3194041 : CollatzResearch.WordTrace tailWord_3194041 prefixEnd_3194041 1640078263167443033598379 := by
  unfold tailWord_3194041
  simp only [CollatzResearch.WordTrace]
  refine ⟨116496245821542430618533977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77664163881028287079022651 116496245821542430618533977)
  ·
    refine ⟨87372184366156822963900483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116496245821542430618533977 87372184366156822963900483)
    ·
      refine ⟨131058276549235234445850725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87372184366156822963900483 131058276549235234445850725)
      ·
        refine ⟨24573426852981606458597011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131058276549235234445850725 24573426852981606458597011)
        ·
          refine ⟨36860140279472409687895517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24573426852981606458597011 36860140279472409687895517)
          ·
            refine ⟨13822552604802153632960819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36860140279472409687895517 13822552604802153632960819)
            ·
              refine ⟨20733828907203230449441229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822552604802153632960819 20733828907203230449441229)
              ·
                refine ⟨7775185840201211418540461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20733828907203230449441229 7775185840201211418540461)
                ·
                  refine ⟨2915694690075454281952673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7775185840201211418540461 2915694690075454281952673)
                  ·
                    refine ⟨2186771017556590711464505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2915694690075454281952673 2186771017556590711464505)
                    ·
                      refine ⟨1640078263167443033598379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186771017556590711464505 1640078263167443033598379)
                      ·
                        rfl

theorem cell23_3194041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3194041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194041 prefixEnd_3194041 := by exact prefixLift 3194041
  have htrace : WordTrace (prefixWord ++ tailWord_3194041) baseStart_3194041 baseEnd_3194041 := by
    simpa [prefixWord, tailWord_3194041, baseEnd_3194041] using wordTrace_append hprefix tailTrace_3194041
  have hstable : (prefixWord ++ tailWord_3194041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194041).length < 2 ^ (prefixWord ++ tailWord_3194041).sum := by decide
  have hdescent : baseEnd_3194041 < baseStart_3194041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194044 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3194044 : Nat := 118140960795 + 3194044 * 2 ^ 59
def prefixEnd_3194044 : Nat := 4983230072969 + 3 ^ 40 * 3194044 * 2
def baseEnd_3194044 : Nat := 1640079803609406521860865

theorem tailTrace_3194044 : CollatzResearch.WordTrace tailWord_3194044 prefixEnd_3194044 1640079803609406521860865 := by
  unfold tailWord_3194044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58248177620265781065446593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77664236827021041420595457 58248177620265781065446593)
  ·
    refine ⟨43686133215199335799084945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58248177620265781065446593 43686133215199335799084945)
    ·
      refine ⟨32764599911399501849313709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43686133215199335799084945 32764599911399501849313709)
      ·
        refine ⟨12286724966774813193492641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32764599911399501849313709 12286724966774813193492641)
        ·
          refine ⟨9215043725081109895119481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12286724966774813193492641 9215043725081109895119481)
          ·
            refine ⟨6911282793810832421339611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9215043725081109895119481 6911282793810832421339611)
            ·
              refine ⟨10366924190716248632009417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911282793810832421339611 10366924190716248632009417)
              ·
                refine ⟨7775193143037186474007063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10366924190716248632009417 7775193143037186474007063)
                ·
                  refine ⟨11662789714555779711010595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7775193143037186474007063 11662789714555779711010595)
                  ·
                    refine ⟨17494184571833669566515893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11662789714555779711010595 17494184571833669566515893)
                    ·
                      refine ⟨1640079803609406521860865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17494184571833669566515893 1640079803609406521860865)
                      ·
                        rfl

theorem cell23_3194044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3194044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194044 prefixEnd_3194044 := by exact prefixLift 3194044
  have htrace : WordTrace (prefixWord ++ tailWord_3194044) baseStart_3194044 baseEnd_3194044 := by
    simpa [prefixWord, tailWord_3194044, baseEnd_3194044] using wordTrace_append hprefix tailTrace_3194044
  have hstable : (prefixWord ++ tailWord_3194044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194044).length < 2 ^ (prefixWord ++ tailWord_3194044).sum := by decide
  have hdescent : baseEnd_3194044 < baseStart_3194044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194097 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3194097 : Nat := 118140960795 + 3194097 * 2 ^ 59
def prefixEnd_3194097 : Nat := 4983230072969 + 3 ^ 40 * 3194097 * 2
def baseEnd_3194097 : Nat := 1640107018084094814498121

theorem tailTrace_3194097 : CollatzResearch.WordTrace tailWord_3194097 prefixEnd_3194097 1640107018084094814498121 := by
  unfold tailWord_3194097
  simp only [CollatzResearch.WordTrace]
  refine ⟨116498288309339552182572545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77665525539559701455048363 116498288309339552182572545)
  ·
    refine ⟨87373716232004664136929409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116498288309339552182572545 87373716232004664136929409)
    ·
      refine ⟨65530287174003498102697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87373716232004664136929409 65530287174003498102697057)
      ·
        refine ⟨49147715380502623577022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65530287174003498102697057 49147715380502623577022793)
        ·
          refine ⟨36860786535376967682767095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49147715380502623577022793 36860786535376967682767095)
          ·
            refine ⟨55291179803065451524150643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36860786535376967682767095 55291179803065451524150643)
            ·
              refine ⟨82936769704598177286225965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55291179803065451524150643 82936769704598177286225965)
              ·
                refine ⟨31101288639224316482334737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82936769704598177286225965 31101288639224316482334737)
                ·
                  refine ⟨23325966479418237361751053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31101288639224316482334737 23325966479418237361751053)
                  ·
                    refine ⟨8747237429781839010656645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23325966479418237361751053 8747237429781839010656645)
                    ·
                      refine ⟨1640107018084094814498121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8747237429781839010656645 1640107018084094814498121)
                      ·
                        rfl

theorem cell23_3194097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3194097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194097 prefixEnd_3194097 := by exact prefixLift 3194097
  have htrace : WordTrace (prefixWord ++ tailWord_3194097) baseStart_3194097 baseEnd_3194097 := by
    simpa [prefixWord, tailWord_3194097, baseEnd_3194097] using wordTrace_append hprefix tailTrace_3194097
  have hstable : (prefixWord ++ tailWord_3194097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194097).length < 2 ^ (prefixWord ++ tailWord_3194097).sum := by decide
  have hdescent : baseEnd_3194097 < baseStart_3194097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194108 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_3194108 : Nat := 118140960795 + 3194108 * 2 ^ 59
def prefixEnd_3194108 : Nat := 4983230072969 + 3 ^ 40 * 3194108 * 2
def baseEnd_3194108 : Nat := 1640112666371294271460571

theorem tailTrace_3194108 : CollatzResearch.WordTrace tailWord_3194108 prefixEnd_3194108 1640112666371294271460571 := by
  unfold tailWord_3194108
  simp only [CollatzResearch.WordTrace]
  refine ⟨58249344756149850530611489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77665793008199800707481985 58249344756149850530611489)
  ·
    refine ⟨43687008567112387897958617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58249344756149850530611489 43687008567112387897958617)
    ·
      refine ⟨32765256425334290923468963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43687008567112387897958617 32765256425334290923468963)
      ·
        refine ⟨49147884638001436385203445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32765256425334290923468963 49147884638001436385203445)
        ·
          refine ⟨4607614184812634661112823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49147884638001436385203445 4607614184812634661112823)
          ·
            refine ⟨6911421277218951991669235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607614184812634661112823 6911421277218951991669235)
            ·
              refine ⟨10367131915828427987503853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911421277218951991669235 10367131915828427987503853)
              ·
                refine ⟨3887674468435660495313945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10367131915828427987503853 3887674468435660495313945)
                ·
                  refine ⟨2915755851326745371485459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887674468435660495313945 2915755851326745371485459)
                  ·
                    refine ⟨4373633776990118057228189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915755851326745371485459 4373633776990118057228189)
                    ·
                      refine ⟨1640112666371294271460571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373633776990118057228189 1640112666371294271460571)
                      ·
                        rfl

theorem cell23_3194108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_3194108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194108 prefixEnd_3194108 := by exact prefixLift 3194108
  have htrace : WordTrace (prefixWord ++ tailWord_3194108) baseStart_3194108 baseEnd_3194108 := by
    simpa [prefixWord, tailWord_3194108, baseEnd_3194108] using wordTrace_append hprefix tailTrace_3194108
  have hstable : (prefixWord ++ tailWord_3194108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194108).length < 2 ^ (prefixWord ++ tailWord_3194108).sum := by decide
  have hdescent : baseEnd_3194108 < baseStart_3194108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194117 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_3194117 : Nat := 118140960795 + 3194117 * 2 ^ 59
def prefixEnd_3194117 : Nat := 4983230072969 + 3 ^ 40 * 3194117 * 2
def baseEnd_3194117 : Nat := 1640117287697184736248029

theorem tailTrace_3194117 : CollatzResearch.WordTrace tailWord_3194117 prefixEnd_3194117 1640117287697184736248029 := by
  unfold tailWord_3194117
  simp only [CollatzResearch.WordTrace]
  refine ⟨116499017769267095598300605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77666011846178063732200403 116499017769267095598300605)
  ·
    refine ⟨43687131663475160849362727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116499017769267095598300605 43687131663475160849362727)
    ·
      refine ⟨65530697495212741274044091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43687131663475160849362727 65530697495212741274044091)
      ·
        refine ⟨98296046242819111911066137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65530697495212741274044091 98296046242819111911066137)
        ·
          refine ⟨73722034682114333933299603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98296046242819111911066137 73722034682114333933299603)
          ·
            refine ⟨110583052023171500899949405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73722034682114333933299603 110583052023171500899949405)
            ·
              refine ⟨41468644508689312837481027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110583052023171500899949405 41468644508689312837481027)
              ·
                refine ⟨62202966763033969256221541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41468644508689312837481027 62202966763033969256221541)
                ·
                  refine ⟨11663056268068869235541539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62202966763033969256221541 11663056268068869235541539)
                  ·
                    refine ⟨17494584402103303853312309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11663056268068869235541539 17494584402103303853312309)
                    ·
                      refine ⟨1640117287697184736248029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17494584402103303853312309 1640117287697184736248029)
                      ·
                        rfl

theorem cell23_3194117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_3194117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194117 prefixEnd_3194117 := by exact prefixLift 3194117
  have htrace : WordTrace (prefixWord ++ tailWord_3194117) baseStart_3194117 baseEnd_3194117 := by
    simpa [prefixWord, tailWord_3194117, baseEnd_3194117] using wordTrace_append hprefix tailTrace_3194117
  have hstable : (prefixWord ++ tailWord_3194117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194117).length < 2 ^ (prefixWord ++ tailWord_3194117).sum := by decide
  have hdescent : baseEnd_3194117 < baseStart_3194117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194127 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_3194127 : Nat := 118140960795 + 3194127 * 2 ^ 59
def prefixEnd_3194127 : Nat := 4983230072969 + 3 ^ 40 * 3194127 * 2
def baseEnd_3194127 : Nat := 1640122422503729697122983

theorem tailTrace_3194127 : CollatzResearch.WordTrace tailWord_3194127 prefixEnd_3194127 1640122422503729697122983 := by
  unfold tailWord_3194127
  simp only [CollatzResearch.WordTrace]
  refine ⟨116499382499230867306164635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77666254999487244870776423 116499382499230867306164635)
  ·
    refine ⟨174749073748846300959246953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116499382499230867306164635 174749073748846300959246953)
    ·
      refine ⟨131061805311634725719435215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174749073748846300959246953 131061805311634725719435215)
      ·
        refine ⟨196592707967452088579152823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131061805311634725719435215 196592707967452088579152823)
        ·
          refine ⟨294889061951178132868729235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196592707967452088579152823 294889061951178132868729235)
          ·
            refine ⟨442333592926767199303093853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294889061951178132868729235 442333592926767199303093853)
            ·
              refine ⟨165875097347537699738660195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442333592926767199303093853 165875097347537699738660195)
              ·
                refine ⟨248812646021306549607990293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165875097347537699738660195 248812646021306549607990293)
                ·
                  refine ⟨11663092782248744512874545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248812646021306549607990293 11663092782248744512874545)
                  ·
                    refine ⟨8747319586686558384655909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11663092782248744512874545 8747319586686558384655909)
                    ·
                      refine ⟨1640122422503729697122983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8747319586686558384655909 1640122422503729697122983)
                      ·
                        rfl

theorem cell23_3194127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_3194127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194127 prefixEnd_3194127 := by exact prefixLift 3194127
  have htrace : WordTrace (prefixWord ++ tailWord_3194127) baseStart_3194127 baseEnd_3194127 := by
    simpa [prefixWord, tailWord_3194127, baseEnd_3194127] using wordTrace_append hprefix tailTrace_3194127
  have hstable : (prefixWord ++ tailWord_3194127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194127).length < 2 ^ (prefixWord ++ tailWord_3194127).sum := by decide
  have hdescent : baseEnd_3194127 < baseStart_3194127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194142 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3194142 : Nat := 118140960795 + 3194142 * 2 ^ 59
def prefixEnd_3194142 : Nat := 4983230072969 + 3 ^ 40 * 3194142 * 2
def baseEnd_3194142 : Nat := 1640130124713547138435415

theorem tailTrace_3194142 : CollatzResearch.WordTrace tailWord_3194142 prefixEnd_3194142 1640130124713547138435415 := by
  unfold tailWord_3194142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562491199272065608495085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77666619729451016578640453 14562491199272065608495085)
  ·
    refine ⟨5460934199727024603185657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14562491199272065608495085 5460934199727024603185657)
    ·
      refine ⟨4095700649795268452389243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5460934199727024603185657 4095700649795268452389243)
      ·
        refine ⟨6143550974692902678583865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095700649795268452389243 6143550974692902678583865)
        ·
          refine ⟨4607663231019677008937899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6143550974692902678583865 4607663231019677008937899)
          ·
            refine ⟨6911494846529515513406849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607663231019677008937899 6911494846529515513406849)
            ·
              refine ⟨5183621134897136635055137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911494846529515513406849 5183621134897136635055137)
              ·
                refine ⟨3887715851172852476291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183621134897136635055137 3887715851172852476291353)
                ·
                  refine ⟨2915786888379639357218515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887715851172852476291353 2915786888379639357218515)
                  ·
                    refine ⟨4373680332569459035827773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915786888379639357218515 4373680332569459035827773)
                    ·
                      refine ⟨1640130124713547138435415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373680332569459035827773 1640130124713547138435415)
                      ·
                        rfl

theorem cell23_3194142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3194142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194142 prefixEnd_3194142 := by exact prefixLift 3194142
  have htrace : WordTrace (prefixWord ++ tailWord_3194142) baseStart_3194142 baseEnd_3194142 := by
    simpa [prefixWord, tailWord_3194142, baseEnd_3194142] using wordTrace_append hprefix tailTrace_3194142
  have hstable : (prefixWord ++ tailWord_3194142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194142).length < 2 ^ (prefixWord ++ tailWord_3194142).sum := by decide
  have hdescent : baseEnd_3194142 < baseStart_3194142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194205 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 7]
def baseStart_3194205 : Nat := 118140960795 + 3194205 * 2 ^ 59
def prefixEnd_3194205 : Nat := 4983230072969 + 3 ^ 40 * 3194205 * 2
def baseEnd_3194205 : Nat := 182240274888308932438625

theorem tailTrace_3194205 : CollatzResearch.WordTrace tailWord_3194205 prefixEnd_3194205 182240274888308932438625 := by
  unfold tailWord_3194205
  simp only [CollatzResearch.WordTrace]
  refine ⟨116502227392948286627504069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77668151595298857751669379 116502227392948286627504069)
  ·
    refine ⟨21844167636177803742657013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116502227392948286627504069 21844167636177803742657013)
    ·
      refine ⟨2047890715891669100874095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21844167636177803742657013 2047890715891669100874095)
      ·
        refine ⟨3071836073837503651311143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047890715891669100874095 3071836073837503651311143)
        ·
          refine ⟨4607754110756255476966715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071836073837503651311143 4607754110756255476966715)
          ·
            refine ⟨6911631166134383215450073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607754110756255476966715 6911631166134383215450073)
            ·
              refine ⟨5183723374600787411587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911631166134383215450073 5183723374600787411587555)
              ·
                refine ⟨7775585061901181117381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183723374600787411587555 7775585061901181117381333)
                ·
                  refine ⟨182240274888308932438625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7775585061901181117381333 182240274888308932438625)
                  ·
                    rfl

theorem cell23_3194205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_3194205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194205 prefixEnd_3194205 := by exact prefixLift 3194205
  have htrace : WordTrace (prefixWord ++ tailWord_3194205) baseStart_3194205 baseEnd_3194205 := by
    simpa [prefixWord, tailWord_3194205, baseEnd_3194205] using wordTrace_append hprefix tailTrace_3194205
  have hstable : (prefixWord ++ tailWord_3194205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194205).length < 2 ^ (prefixWord ++ tailWord_3194205).sum := by decide
  have hdescent : baseEnd_3194205 < baseStart_3194205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194224 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_3194224 : Nat := 118140960795 + 3194224 * 2 ^ 59
def prefixEnd_3194224 : Nat := 4983230072969 + 3 ^ 40 * 3194224 * 2
def baseEnd_3194224 : Nat := 1640172230127215817610037

theorem tailTrace_3194224 : CollatzResearch.WordTrace tailWord_3194224 prefixEnd_3194224 1640172230127215817610037 := by
  unfold tailWord_3194224
  simp only [CollatzResearch.WordTrace]
  refine ⟨58251460189939726436222863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77668613586586301914963817 58251460189939726436222863)
  ·
    refine ⟨87377190284909589654334295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58251460189939726436222863 87377190284909589654334295)
    ·
      refine ⟨131065785427364384481501443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87377190284909589654334295 131065785427364384481501443)
      ·
        refine ⟨196598678141046576722252165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131065785427364384481501443 196598678141046576722252165)
        ·
          refine ⟨36862252151446233135422281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196598678141046576722252165 36862252151446233135422281)
          ·
            refine ⟨27646689113584674851566711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36862252151446233135422281 27646689113584674851566711)
            ·
              refine ⟨41470033670377012277350067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27646689113584674851566711 41470033670377012277350067)
              ·
                refine ⟨62205050505565518416025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41470033670377012277350067 62205050505565518416025101)
                ·
                  refine ⟨23326893939587069406009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62205050505565518416025101 23326893939587069406009413)
                  ·
                    refine ⟨4373792613672575513626765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23326893939587069406009413 4373792613672575513626765)
                    ·
                      refine ⟨1640172230127215817610037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373792613672575513626765 1640172230127215817610037)
                      ·
                        rfl

theorem cell23_3194224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_3194224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194224 prefixEnd_3194224 := by exact prefixLift 3194224
  have htrace : WordTrace (prefixWord ++ tailWord_3194224) baseStart_3194224 baseEnd_3194224 := by
    simpa [prefixWord, tailWord_3194224, baseEnd_3194224] using wordTrace_append hprefix tailTrace_3194224
  have hstable : (prefixWord ++ tailWord_3194224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194224).length < 2 ^ (prefixWord ++ tailWord_3194224).sum := by decide
  have hdescent : baseEnd_3194224 < baseStart_3194224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194227 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 12]
def baseStart_3194227 : Nat := 118140960795 + 3194227 * 2 ^ 59
def prefixEnd_3194227 : Nat := 4983230072969 + 3 ^ 40 * 3194227 * 2
def baseEnd_3194227 : Nat := 182241530063242145096947

theorem tailTrace_3194227 : CollatzResearch.WordTrace tailWord_3194227 prefixEnd_3194227 182241530063242145096947 := by
  unfold tailWord_3194227
  simp only [CollatzResearch.WordTrace]
  refine ⟨116503029798868584384804935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77668686532579056256536623 116503029798868584384804935)
  ·
    refine ⟨174754544698302876577207403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116503029798868584384804935 174754544698302876577207403)
    ·
      refine ⟨262131817047454314865811105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174754544698302876577207403 262131817047454314865811105)
      ·
        refine ⟨196598862785590736149358329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262131817047454314865811105 196598862785590736149358329)
        ·
          refine ⟨147449147089193052112018747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196598862785590736149358329 147449147089193052112018747)
          ·
            refine ⟨221173720633789578168028121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147449147089193052112018747 221173720633789578168028121)
            ·
              refine ⟨165880290475342183626021091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221173720633789578168028121 165880290475342183626021091)
              ·
                refine ⟨248820435713013275439031637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165880290475342183626021091 248820435713013275439031637)
                ·
                  refine ⟨182241530063242145096947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 248820435713013275439031637 182241530063242145096947)
                  ·
                    rfl

theorem cell23_3194227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 12].length) (baseStart_3194227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194227 prefixEnd_3194227 := by exact prefixLift 3194227
  have htrace : WordTrace (prefixWord ++ tailWord_3194227) baseStart_3194227 baseEnd_3194227 := by
    simpa [prefixWord, tailWord_3194227, baseEnd_3194227] using wordTrace_append hprefix tailTrace_3194227
  have hstable : (prefixWord ++ tailWord_3194227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194227).length < 2 ^ (prefixWord ++ tailWord_3194227).sum := by decide
  have hdescent : baseEnd_3194227 < baseStart_3194227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194244 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3194244 : Nat := 118140960795 + 3194244 * 2 ^ 59
def prefixEnd_3194244 : Nat := 4983230072969 + 3 ^ 40 * 3194244 * 2
def baseEnd_3194244 : Nat := 182242499971145082151105

theorem tailTrace_3194244 : CollatzResearch.WordTrace tailWord_3194244 prefixEnd_3194244 182242499971145082151105 := by
  unfold tailWord_3194244
  simp only [CollatzResearch.WordTrace]
  refine ⟨58251824919903498144086893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77669099893204664192115857 58251824919903498144086893)
  ·
    refine ⟨21844434344963811804032585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58251824919903498144086893 21844434344963811804032585)
    ·
      refine ⟨16383325758722858853024439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21844434344963811804032585 16383325758722858853024439)
      ·
        refine ⟨24574988638084288279536659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383325758722858853024439 24574988638084288279536659)
        ·
          refine ⟨36862482957126432419304989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24574988638084288279536659 36862482957126432419304989)
          ·
            refine ⟨13823431108922412157239371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36862482957126432419304989 13823431108922412157239371)
            ·
              refine ⟨20735146663383618235859057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13823431108922412157239371 20735146663383618235859057)
              ·
                refine ⟨15551359997537713676894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20735146663383618235859057 15551359997537713676894293)
                ·
                  refine ⟨182242499971145082151105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15551359997537713676894293 182242499971145082151105)
                  ·
                    rfl

theorem cell23_3194244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3194244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194244 prefixEnd_3194244 := by exact prefixLift 3194244
  have htrace : WordTrace (prefixWord ++ tailWord_3194244) baseStart_3194244 baseEnd_3194244 := by
    simpa [prefixWord, tailWord_3194244, baseEnd_3194244] using wordTrace_append hprefix tailTrace_3194244
  have hstable : (prefixWord ++ tailWord_3194244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194244).length < 2 ^ (prefixWord ++ tailWord_3194244).sum := by decide
  have hdescent : baseEnd_3194244 < baseStart_3194244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194265 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 1, 4]
def baseStart_3194265 : Nat := 118140960795 + 3194265 * 2 ^ 59
def prefixEnd_3194265 : Nat := 4983230072969 + 3 ^ 40 * 3194265 * 2
def baseEnd_3194265 : Nat := 546731094278016719065783

theorem tailTrace_3194265 : CollatzResearch.WordTrace tailWord_3194265 prefixEnd_3194265 546731094278016719065783 := by
  unfold tailWord_3194265
  simp only [CollatzResearch.WordTrace]
  refine ⟨116504415772730916874688249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77669610515153944583125499 116504415772730916874688249)
  ·
    refine ⟨87378311829548187656016187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116504415772730916874688249 87378311829548187656016187)
    ·
      refine ⟨131067467744322281484024281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87378311829548187656016187 131067467744322281484024281)
      ·
        refine ⟨98300600808241711113018211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131067467744322281484024281 98300600808241711113018211)
        ·
          refine ⟨147450901212362566669527317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98300600808241711113018211 147450901212362566669527317)
          ·
            refine ⟨6911760994329495312634093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147450901212362566669527317 6911760994329495312634093)
            ·
              refine ⟨2591910372873560742237785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6911760994329495312634093 2591910372873560742237785)
              ·
                refine ⟨1943932779655170556678339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591910372873560742237785 1943932779655170556678339)
                ·
                  refine ⟨2915899169482755835017509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943932779655170556678339 2915899169482755835017509)
                  ·
                    refine ⟨546731094278016719065783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915899169482755835017509 546731094278016719065783)
                    ·
                      rfl

theorem cell23_3194265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_3194265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194265 prefixEnd_3194265 := by exact prefixLift 3194265
  have htrace : WordTrace (prefixWord ++ tailWord_3194265) baseStart_3194265 baseEnd_3194265 := by
    simpa [prefixWord, tailWord_3194265, baseEnd_3194265] using wordTrace_append hprefix tailTrace_3194265
  have hstable : (prefixWord ++ tailWord_3194265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194265).length < 2 ^ (prefixWord ++ tailWord_3194265).sum := by decide
  have hdescent : baseEnd_3194265 < baseStart_3194265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194304 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_3194304 : Nat := 118140960795 + 3194304 * 2 ^ 59
def prefixEnd_3194304 : Nat := 4983230072969 + 3 ^ 40 * 3194304 * 2
def baseEnd_3194304 : Nat := 546737769526525168203223

theorem tailTrace_3194304 : CollatzResearch.WordTrace tailWord_3194304 prefixEnd_3194304 546737769526525168203223 := by
  unfold tailWord_3194304
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252919109794813267678983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77670558813059751023571977 58252919109794813267678983)
  ·
    refine ⟨87379378664692219901518475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58252919109794813267678983 87379378664692219901518475)
    ·
      refine ⟨131069067997038329852277713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87379378664692219901518475 131069067997038329852277713)
      ·
        refine ⟨98301800997778747389208285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131069067997038329852277713 98301800997778747389208285)
        ·
          refine ⟨36863175374167030270953107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98301800997778747389208285 36863175374167030270953107)
          ·
            refine ⟨55294763061250545406429661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36863175374167030270953107 55294763061250545406429661)
            ·
              refine ⟨20735536147968954527411123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55294763061250545406429661 20735536147968954527411123)
              ·
                refine ⟨31103304221953431791116685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20735536147968954527411123 31103304221953431791116685)
                ·
                  refine ⟨11663739083232536921668757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31103304221953431791116685 11663739083232536921668757)
                  ·
                    refine ⟨546737769526525168203223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11663739083232536921668757 546737769526525168203223)
                    ·
                      rfl

theorem cell23_3194304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_3194304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194304 prefixEnd_3194304 := by exact prefixLift 3194304
  have htrace : WordTrace (prefixWord ++ tailWord_3194304) baseStart_3194304 baseEnd_3194304 := by
    simpa [prefixWord, tailWord_3194304, baseEnd_3194304] using wordTrace_append hprefix tailTrace_3194304
  have hstable : (prefixWord ++ tailWord_3194304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194304).length < 2 ^ (prefixWord ++ tailWord_3194304).sum := by decide
  have hdescent : baseEnd_3194304 < baseStart_3194304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194349 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3194349 : Nat := 118140960795 + 3194349 * 2 ^ 59
def prefixEnd_3194349 : Nat := 4983230072969 + 3 ^ 40 * 3194349 * 2
def baseEnd_3194349 : Nat := 1640236415209027828546963

theorem tailTrace_3194349 : CollatzResearch.WordTrace tailWord_3194349 prefixEnd_3194349 1640236415209027828546963 := by
  unfold tailWord_3194349
  simp only [CollatzResearch.WordTrace]
  refine ⟨116507479504426599220746101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77671653002951066147164067 116507479504426599220746101)
  ·
    refine ⟨10922576203539993676944947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116507479504426599220746101 10922576203539993676944947)
    ·
      refine ⟨16383864305309990515417421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922576203539993676944947 16383864305309990515417421)
      ·
        refine ⟨6143949114491246443281533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16383864305309990515417421 6143949114491246443281533)
        ·
          refine ⟨2303980917934217416230575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6143949114491246443281533 2303980917934217416230575)
          ·
            refine ⟨3455971376901326124345863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303980917934217416230575 3455971376901326124345863)
            ·
              refine ⟨5183957065351989186518795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455971376901326124345863 5183957065351989186518795)
              ·
                refine ⟨7775935598027983779778193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183957065351989186518795 7775935598027983779778193)
                ·
                  refine ⟨5831951698520987834833645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775935598027983779778193 5831951698520987834833645)
                  ·
                    refine ⟨2186981886945370438062617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5831951698520987834833645 2186981886945370438062617)
                    ·
                      refine ⟨1640236415209027828546963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186981886945370438062617 1640236415209027828546963)
                      ·
                        rfl

theorem cell23_3194349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3194349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194349 prefixEnd_3194349 := by exact prefixLift 3194349
  have htrace : WordTrace (prefixWord ++ tailWord_3194349) baseStart_3194349 baseEnd_3194349 := by
    simpa [prefixWord, tailWord_3194349, baseEnd_3194349] using wordTrace_append hprefix tailTrace_3194349
  have hstable : (prefixWord ++ tailWord_3194349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194349).length < 2 ^ (prefixWord ++ tailWord_3194349).sum := by decide
  have hdescent : baseEnd_3194349 < baseStart_3194349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194358 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3194358 : Nat := 118140960795 + 3194358 * 2 ^ 59
def prefixEnd_3194358 : Nat := 4983230072969 + 3 ^ 40 * 3194358 * 2
def baseEnd_3194358 : Nat := 1640241036534918293334421

theorem tailTrace_3194358 : CollatzResearch.WordTrace tailWord_3194358 prefixEnd_3194358 1640241036534918293334421 := by
  unfold tailWord_3194358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281737985087124609863983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77671871840929329171882485 7281737985087124609863983)
  ·
    refine ⟨10922606977630686914795975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7281737985087124609863983 10922606977630686914795975)
    ·
      refine ⟨16383910466446030372193963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922606977630686914795975 16383910466446030372193963)
      ·
        refine ⟨24575865699669045558290945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383910466446030372193963 24575865699669045558290945)
        ·
          refine ⟨18431899274751784168718209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24575865699669045558290945 18431899274751784168718209)
          ·
            refine ⟨13823924456063838126538657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18431899274751784168718209 13823924456063838126538657)
            ·
              refine ⟨10367943342047878594903993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13823924456063838126538657 10367943342047878594903993)
              ·
                refine ⟨7775957506535908946177995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10367943342047878594903993 7775957506535908946177995)
                ·
                  refine ⟨11663936259803863419266993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7775957506535908946177995 11663936259803863419266993)
                  ·
                    refine ⟨8747952194852897564450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11663936259803863419266993 8747952194852897564450245)
                    ·
                      refine ⟨1640241036534918293334421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8747952194852897564450245 1640241036534918293334421)
                      ·
                        rfl

theorem cell23_3194358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3194358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194358 prefixEnd_3194358 := by exact prefixLift 3194358
  have htrace : WordTrace (prefixWord ++ tailWord_3194358) baseStart_3194358 baseEnd_3194358 := by
    simpa [prefixWord, tailWord_3194358, baseEnd_3194358] using wordTrace_append hprefix tailTrace_3194358
  have hstable : (prefixWord ++ tailWord_3194358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194358).length < 2 ^ (prefixWord ++ tailWord_3194358).sum := by decide
  have hdescent : baseEnd_3194358 < baseStart_3194358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194362 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_3194362 : Nat := 118140960795 + 3194362 * 2 ^ 59
def prefixEnd_3194362 : Nat := 4983230072969 + 3 ^ 40 * 3194362 * 2
def baseEnd_3194362 : Nat := 1640243090457536277684403

theorem tailTrace_3194362 : CollatzResearch.WordTrace tailWord_3194362 prefixEnd_3194362 1640243090457536277684403 := by
  unfold tailWord_3194362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29126988413344875610242335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77671969102253001627312893 29126988413344875610242335)
  ·
    refine ⟨43690482620017313415363503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29126988413344875610242335 43690482620017313415363503)
    ·
      refine ⟨65535723930025970123045255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43690482620017313415363503 65535723930025970123045255)
      ·
        refine ⟨98303585895038955184567883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65535723930025970123045255 98303585895038955184567883)
        ·
          refine ⟨147455378842558432776851825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98303585895038955184567883 147455378842558432776851825)
          ·
            refine ⟨110591534131918824582638869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147455378842558432776851825 110591534131918824582638869)
            ·
              refine ⟨5183978162433694902311197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110591534131918824582638869 5183978162433694902311197)
              ·
                refine ⟨1943991810912635588366699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5183978162433694902311197 1943991810912635588366699)
                ·
                  refine ⟨2915987716368953382550049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943991810912635588366699 2915987716368953382550049)
                  ·
                    refine ⟨2186990787276715036912537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2915987716368953382550049 2186990787276715036912537)
                    ·
                      refine ⟨1640243090457536277684403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2186990787276715036912537 1640243090457536277684403)
                      ·
                        rfl

theorem cell23_3194362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_3194362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194362 prefixEnd_3194362 := by exact prefixLift 3194362
  have htrace : WordTrace (prefixWord ++ tailWord_3194362) baseStart_3194362 baseEnd_3194362 := by
    simpa [prefixWord, tailWord_3194362, baseEnd_3194362] using wordTrace_append hprefix tailTrace_3194362
  have hstable : (prefixWord ++ tailWord_3194362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194362).length < 2 ^ (prefixWord ++ tailWord_3194362).sum := by decide
  have hdescent : baseEnd_3194362 < baseStart_3194362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194365 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_3194365 : Nat := 118140960795 + 3194365 * 2 ^ 59
def prefixEnd_3194365 : Nat := 4983230072969 + 3 ^ 40 * 3194365 * 2
def baseEnd_3194365 : Nat := 1640244630899499765946889

theorem tailTrace_3194365 : CollatzResearch.WordTrace tailWord_3194365 prefixEnd_3194365 1640244630899499765946889 := by
  unfold tailWord_3194365
  simp only [CollatzResearch.WordTrace]
  refine ⟨116508063072368633953328549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77672042048245755968885699 116508063072368633953328549)
  ·
    refine ⟨21845261826069118866249103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116508063072368633953328549 21845261826069118866249103)
    ·
      refine ⟨32767892739103678299373655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21845261826069118866249103 32767892739103678299373655)
      ·
        refine ⟨49151839108655517449060483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32767892739103678299373655 49151839108655517449060483)
        ·
          refine ⟨73727758662983276173590725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49151839108655517449060483 73727758662983276173590725)
          ·
            refine ⟨13823954749309364282548261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73727758662983276173590725 13823954749309364282548261)
            ·
              refine ⟨2591991515495505802977799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13823954749309364282548261 2591991515495505802977799)
              ·
                refine ⟨3887987273243258704466699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591991515495505802977799 3887987273243258704466699)
                ·
                  refine ⟨5831980909864888056700049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887987273243258704466699 5831980909864888056700049)
                  ·
                    refine ⟨4373985682398666042525037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5831980909864888056700049 4373985682398666042525037)
                    ·
                      refine ⟨1640244630899499765946889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4373985682398666042525037 1640244630899499765946889)
                      ·
                        rfl

theorem cell23_3194365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_3194365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194365 prefixEnd_3194365 := by exact prefixLift 3194365
  have htrace : WordTrace (prefixWord ++ tailWord_3194365) baseStart_3194365 baseEnd_3194365 := by
    simpa [prefixWord, tailWord_3194365, baseEnd_3194365] using wordTrace_append hprefix tailTrace_3194365
  have hstable : (prefixWord ++ tailWord_3194365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194365).length < 2 ^ (prefixWord ++ tailWord_3194365).sum := by decide
  have hdescent : baseEnd_3194365 < baseStart_3194365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194372 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_3194372 : Nat := 118140960795 + 3194372 * 2 ^ 59
def prefixEnd_3194372 : Nat := 4983230072969 + 3 ^ 40 * 3194372 * 2
def baseEnd_3194372 : Nat := 546749408421360412853119

theorem tailTrace_3194372 : CollatzResearch.WordTrace tailWord_3194372 prefixEnd_3194372 546749408421360412853119 := by
  unfold tailWord_3194372
  simp only [CollatzResearch.WordTrace]
  refine ⟨58254159191671637074416685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77672212255562182765888913 58254159191671637074416685)
  ·
    refine ⟨21845309696876863902906257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58254159191671637074416685 21845309696876863902906257)
    ·
      refine ⟨16383982272657647927179693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21845309696876863902906257 16383982272657647927179693)
      ·
        refine ⟨6143993352246617972692385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16383982272657647927179693 6143993352246617972692385)
        ·
          refine ⟨4607995014184963479519289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6143993352246617972692385 4607995014184963479519289)
          ·
            refine ⟨3455996260638722609639467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607995014184963479519289 3455996260638722609639467)
            ·
              refine ⟨5183994390958083914459201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455996260638722609639467 5183994390958083914459201)
              ·
                refine ⟨3887995793218562935844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183994390958083914459201 3887995793218562935844401)
                ·
                  refine ⟨2915996844913922201883301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887995793218562935844401 2915996844913922201883301)
                  ·
                    refine ⟨546749408421360412853119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915996844913922201883301 546749408421360412853119)
                    ·
                      rfl

theorem cell23_3194372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_3194372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194372 prefixEnd_3194372 := by exact prefixLift 3194372
  have htrace : WordTrace (prefixWord ++ tailWord_3194372) baseStart_3194372 baseEnd_3194372 := by
    simpa [prefixWord, tailWord_3194372, baseEnd_3194372] using wordTrace_append hprefix tailTrace_3194372
  have hstable : (prefixWord ++ tailWord_3194372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194372).length < 2 ^ (prefixWord ++ tailWord_3194372).sum := by decide
  have hdescent : baseEnd_3194372 < baseStart_3194372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194418 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_3194418 : Nat := 118140960795 + 3194418 * 2 ^ 59
def prefixEnd_3194418 : Nat := 4983230072969 + 3 ^ 40 * 3194418 * 2
def baseEnd_3194418 : Nat := 1640271845374188058584145

theorem tailTrace_3194418 : CollatzResearch.WordTrace tailWord_3194418 prefixEnd_3194418 1640271845374188058584145 := by
  unfold tailWord_3194418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127499035294156001251977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77673330760784416003338605 29127499035294156001251977)
  ·
    refine ⟨21845624276470617000938983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29127499035294156001251977 21845624276470617000938983)
    ·
      refine ⟨32768436414705925501408475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21845624276470617000938983 32768436414705925501408475)
      ·
        refine ⟨49152654622058888252112713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32768436414705925501408475 49152654622058888252112713)
        ·
          refine ⟨36864490966544166189084535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49152654622058888252112713 36864490966544166189084535)
          ·
            refine ⟨55296736449816249283626803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36864490966544166189084535 55296736449816249283626803)
            ·
              refine ⟨82945104674724373925440205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55296736449816249283626803 82945104674724373925440205)
              ·
                refine ⟨31104414253021640222040077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82945104674724373925440205 31104414253021640222040077)
                ·
                  refine ⟨11664155344883115083265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31104414253021640222040077 11664155344883115083265029)
                  ·
                    refine ⟨2187029127165584078112193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11664155344883115083265029 2187029127165584078112193)
                    ·
                      refine ⟨1640271845374188058584145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187029127165584078112193 1640271845374188058584145)
                      ·
                        rfl

theorem cell23_3194418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_3194418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194418 prefixEnd_3194418 := by exact prefixLift 3194418
  have htrace : WordTrace (prefixWord ++ tailWord_3194418) baseStart_3194418 baseEnd_3194418 := by
    simpa [prefixWord, tailWord_3194418, baseEnd_3194418] using wordTrace_append hprefix tailTrace_3194418
  have hstable : (prefixWord ++ tailWord_3194418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194418).length < 2 ^ (prefixWord ++ tailWord_3194418).sum := by decide
  have hdescent : baseEnd_3194418 < baseStart_3194418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194421 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3194421 : Nat := 118140960795 + 3194421 * 2 ^ 59
def prefixEnd_3194421 : Nat := 4983230072969 + 3 ^ 40 * 3194421 * 2
def baseEnd_3194421 : Nat := 1640273385816151546846631

theorem tailTrace_3194421 : CollatzResearch.WordTrace tailWord_3194421 prefixEnd_3194421 1640273385816151546846631 := by
  unfold tailWord_3194421
  simp only [CollatzResearch.WordTrace]
  refine ⟨116510105560165755517367117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77673403706777170344911411 116510105560165755517367117)
  ·
    refine ⟨43691289585062158319012669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116510105560165755517367117 43691289585062158319012669)
    ·
      refine ⟨16384233594398309369629751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43691289585062158319012669 16384233594398309369629751)
      ·
        refine ⟨24576350391597464054444627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384233594398309369629751 24576350391597464054444627)
        ·
          refine ⟨36864525587396196081666941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24576350391597464054444627 36864525587396196081666941)
          ·
            refine ⟨13824197095273573530625103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36864525587396196081666941 13824197095273573530625103)
            ·
              refine ⟨20736295642910360295937655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13824197095273573530625103 20736295642910360295937655)
              ·
                refine ⟨31104443464365540443906483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20736295642910360295937655 31104443464365540443906483)
                ·
                  refine ⟨46656665196548310665859725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31104443464365540443906483 46656665196548310665859725)
                  ·
                    refine ⟨17496249448705616499697397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46656665196548310665859725 17496249448705616499697397)
                    ·
                      refine ⟨1640273385816151546846631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17496249448705616499697397 1640273385816151546846631)
                      ·
                        rfl

theorem cell23_3194421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3194421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194421 prefixEnd_3194421 := by exact prefixLift 3194421
  have htrace : WordTrace (prefixWord ++ tailWord_3194421) baseStart_3194421 baseEnd_3194421 := by
    simpa [prefixWord, tailWord_3194421, baseEnd_3194421] using wordTrace_append hprefix tailTrace_3194421
  have hstable : (prefixWord ++ tailWord_3194421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194421).length < 2 ^ (prefixWord ++ tailWord_3194421).sum := by decide
  have hdescent : baseEnd_3194421 < baseStart_3194421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194452 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_3194452 : Nat := 118140960795 + 3194452 * 2 ^ 59
def prefixEnd_3194452 : Nat := 4983230072969 + 3 ^ 40 * 3194452 * 2
def baseEnd_3194452 : Nat := 1640289303716440925558989

theorem tailTrace_3194452 : CollatzResearch.WordTrace tailWord_3194452 prefixEnd_3194452 1640289303716440925558989 := by
  unfold tailWord_3194452
  simp only [CollatzResearch.WordTrace]
  refine ⟨58255618111526723905872805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77674157482035631874497073 58255618111526723905872805)
  ·
    refine ⟨10922928395911260732351151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58255618111526723905872805 10922928395911260732351151)
    ·
      refine ⟨16384392593866891098526727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922928395911260732351151 16384392593866891098526727)
      ·
        refine ⟨24576588890800336647790091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384392593866891098526727 24576588890800336647790091)
        ·
          refine ⟨36864883336200504971685137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24576588890800336647790091 36864883336200504971685137)
          ·
            refine ⟨27648662502150378728763853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36864883336200504971685137 27648662502150378728763853)
            ·
              refine ⟨10368248438306392023286445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27648662502150378728763853 10368248438306392023286445)
              ·
                refine ⟨3888093164364897008732417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10368248438306392023286445 3888093164364897008732417)
                ·
                  refine ⟨2916069873273672756549313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3888093164364897008732417 2916069873273672756549313)
                  ·
                    refine ⟨2187052404955254567411985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916069873273672756549313 2187052404955254567411985)
                    ·
                      refine ⟨1640289303716440925558989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187052404955254567411985 1640289303716440925558989)
                      ·
                        rfl

theorem cell23_3194452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_3194452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194452 prefixEnd_3194452 := by exact prefixLift 3194452
  have htrace : WordTrace (prefixWord ++ tailWord_3194452) baseStart_3194452 baseEnd_3194452 := by
    simpa [prefixWord, tailWord_3194452, baseEnd_3194452] using wordTrace_append hprefix tailTrace_3194452
  have hstable : (prefixWord ++ tailWord_3194452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194452).length < 2 ^ (prefixWord ++ tailWord_3194452).sum := by decide
  have hdescent : baseEnd_3194452 < baseStart_3194452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194471 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3194471 : Nat := 118140960795 + 3194471 * 2 ^ 59
def prefixEnd_3194471 : Nat := 4983230072969 + 3 ^ 40 * 3194471 * 2
def baseEnd_3194471 : Nat := 546766353282958783740467

theorem tailTrace_3194471 : CollatzResearch.WordTrace tailWord_3194471 prefixEnd_3194471 546766353282958783740467 := by
  unfold tailWord_3194471
  simp only [CollatzResearch.WordTrace]
  refine ⟨116511929209984614056687267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77674619473323076037791511 116511929209984614056687267)
  ·
    refine ⟨174767893814976921085030901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116511929209984614056687267 174767893814976921085030901)
    ·
      refine ⟨16384490045154086351721647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174767893814976921085030901 16384490045154086351721647)
      ·
        refine ⟨24576735067731129527582471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384490045154086351721647 24576735067731129527582471)
        ·
          refine ⟨36865102601596694291373707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24576735067731129527582471 36865102601596694291373707)
          ·
            refine ⟨55297653902395041437060561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36865102601596694291373707 55297653902395041437060561)
            ·
              refine ⟨41473240426796281077795421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55297653902395041437060561 41473240426796281077795421)
              ·
                refine ⟨15552465160048605404173283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41473240426796281077795421 15552465160048605404173283)
                ·
                  refine ⟨23328697740072908106259925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15552465160048605404173283 23328697740072908106259925)
                  ·
                    refine ⟨546766353282958783740467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23328697740072908106259925 546766353282958783740467)
                    ·
                      rfl

theorem cell23_3194471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3194471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194471 prefixEnd_3194471 := by exact prefixLift 3194471
  have htrace : WordTrace (prefixWord ++ tailWord_3194471) baseStart_3194471 baseEnd_3194471 := by
    simpa [prefixWord, tailWord_3194471, baseEnd_3194471] using wordTrace_append hprefix tailTrace_3194471
  have hstable : (prefixWord ++ tailWord_3194471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194471).length < 2 ^ (prefixWord ++ tailWord_3194471).sum := by decide
  have hdescent : baseEnd_3194471 < baseStart_3194471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194521 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3194521 : Nat := 118140960795 + 3194521 * 2 ^ 59
def prefixEnd_3194521 : Nat := 4983230072969 + 3 ^ 40 * 3194521 * 2
def baseEnd_3194521 : Nat := 1640324733881601155596171

theorem tailTrace_3194521 : CollatzResearch.WordTrace tailWord_3194521 prefixEnd_3194521 1640324733881601155596171 := by
  unfold tailWord_3194521
  simp only [CollatzResearch.WordTrace]
  refine ⟨116513752859803472596007417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77675835239868981730671611 116513752859803472596007417)
  ·
    refine ⟨87385314644852604447005563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116513752859803472596007417 87385314644852604447005563)
    ·
      refine ⟨131077971967278906670508345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87385314644852604447005563 131077971967278906670508345)
      ·
        refine ⟨98308478975459180002881259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131077971967278906670508345 98308478975459180002881259)
        ·
          refine ⟨147462718463188770004321889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98308478975459180002881259 147462718463188770004321889)
          ·
            refine ⟨110597038847391577503241417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147462718463188770004321889 110597038847391577503241417)
            ·
              refine ⟨82947779135543683127431063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110597038847391577503241417 82947779135543683127431063)
              ·
                refine ⟨124421668703315524691146595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82947779135543683127431063 124421668703315524691146595)
                ·
                  refine ⟨186632503054973287036719893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124421668703315524691146595 186632503054973287036719893)
                  ·
                    refine ⟨8748398580701872829846245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186632503054973287036719893 8748398580701872829846245)
                    ·
                      refine ⟨1640324733881601155596171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8748398580701872829846245 1640324733881601155596171)
                      ·
                        rfl

theorem cell23_3194521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3194521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194521 prefixEnd_3194521 := by exact prefixLift 3194521
  have htrace : WordTrace (prefixWord ++ tailWord_3194521) baseStart_3194521 baseEnd_3194521 := by
    simpa [prefixWord, tailWord_3194521, baseEnd_3194521] using wordTrace_append hprefix tailTrace_3194521
  have hstable : (prefixWord ++ tailWord_3194521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194521).length < 2 ^ (prefixWord ++ tailWord_3194521).sum := by decide
  have hdescent : baseEnd_3194521 < baseStart_3194521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194531 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 8]
def baseStart_3194531 : Nat := 118140960795 + 3194531 * 2 ^ 59
def prefixEnd_3194531 : Nat := 4983230072969 + 3 ^ 40 * 3194531 * 2
def baseEnd_3194531 : Nat := 182258874298682901830125

theorem tailTrace_3194531 : CollatzResearch.WordTrace tailWord_3194531 prefixEnd_3194531 182258874298682901830125 := by
  unfold tailWord_3194531
  simp only [CollatzResearch.WordTrace]
  refine ⟨116514117589767244303871447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77676078393178162869247631 116514117589767244303871447)
  ·
    refine ⟨174771176384650866455807171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116514117589767244303871447 174771176384650866455807171)
    ·
      refine ⟨262156764576976299683710757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174771176384650866455807171 262156764576976299683710757)
      ·
        refine ⟨49154393358183056190695767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262156764576976299683710757 49154393358183056190695767)
        ·
          refine ⟨73731590037274584286043651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49154393358183056190695767 73731590037274584286043651)
          ·
            refine ⟨110597385055911876429065477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73731590037274584286043651 110597385055911876429065477)
            ·
              refine ⟨20737009697983476830449777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110597385055911876429065477 20737009697983476830449777)
              ·
                refine ⟨15552757273487607622837333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20737009697983476830449777 15552757273487607622837333)
                ·
                  refine ⟨182258874298682901830125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15552757273487607622837333 182258874298682901830125)
                  ·
                    rfl

theorem cell23_3194531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 8].length) (baseStart_3194531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194531 prefixEnd_3194531 := by exact prefixLift 3194531
  have htrace : WordTrace (prefixWord ++ tailWord_3194531) baseStart_3194531 baseEnd_3194531 := by
    simpa [prefixWord, tailWord_3194531, baseEnd_3194531] using wordTrace_append hprefix tailTrace_3194531
  have hstable : (prefixWord ++ tailWord_3194531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194531).length < 2 ^ (prefixWord ++ tailWord_3194531).sum := by decide
  have hdescent : baseEnd_3194531 < baseStart_3194531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194571 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_3194571 : Nat := 118140960795 + 3194571 * 2 ^ 59
def prefixEnd_3194571 : Nat := 4983230072969 + 3 ^ 40 * 3194571 * 2
def baseEnd_3194571 : Nat := 1640350407914325959970941

theorem tailTrace_3194571 : CollatzResearch.WordTrace tailWord_3194571 prefixEnd_3194571 1640350407914325959970941 := by
  unfold tailWord_3194571
  simp only [CollatzResearch.WordTrace]
  refine ⟨116515576509622331135327567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77677051006414887423551711 116515576509622331135327567)
  ·
    refine ⟨174773364764433496702991351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116515576509622331135327567 174773364764433496702991351)
    ·
      refine ⟨262160047146650245054487027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174773364764433496702991351 262160047146650245054487027)
      ·
        refine ⟨393240070719975367581730541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262160047146650245054487027 393240070719975367581730541)
        ·
          refine ⟨147465026519990762843148953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393240070719975367581730541 147465026519990762843148953)
          ·
            refine ⟨110598769889993072132361715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147465026519990762843148953 110598769889993072132361715)
            ·
              refine ⟨165898154834989608198542573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110598769889993072132361715 165898154834989608198542573)
              ·
                refine ⟨62211808063121103074453465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165898154834989608198542573 62211808063121103074453465)
                ·
                  refine ⟨46658856047340827305840099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62211808063121103074453465 46658856047340827305840099)
                  ·
                    refine ⟨69988284071011240958760149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46658856047340827305840099 69988284071011240958760149)
                    ·
                      refine ⟨1640350407914325959970941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69988284071011240958760149 1640350407914325959970941)
                      ·
                        rfl

theorem cell23_3194571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_3194571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194571 prefixEnd_3194571 := by exact prefixLift 3194571
  have htrace : WordTrace (prefixWord ++ tailWord_3194571) baseStart_3194571 baseEnd_3194571 := by
    simpa [prefixWord, tailWord_3194571, baseEnd_3194571] using wordTrace_append hprefix tailTrace_3194571
  have hstable : (prefixWord ++ tailWord_3194571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194571).length < 2 ^ (prefixWord ++ tailWord_3194571).sum := by decide
  have hdescent : baseEnd_3194571 < baseStart_3194571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194585 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 5, 2]
def baseStart_3194585 : Nat := 118140960795 + 3194585 * 2 ^ 59
def prefixEnd_3194585 : Nat := 4983230072969 + 3 ^ 40 * 3194585 * 2
def baseEnd_3194585 : Nat := 1640357596643488905195877

theorem tailTrace_3194585 : CollatzResearch.WordTrace tailWord_3194585 prefixEnd_3194585 1640357596643488905195877 := by
  unfold tailWord_3194585
  simp only [CollatzResearch.WordTrace]
  refine ⟨116516087131571611526337209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77677391421047741017558139 116516087131571611526337209)
  ·
    refine ⟨87387065348678708644752907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116516087131571611526337209 87387065348678708644752907)
    ·
      refine ⟨131080598023018062967129361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87387065348678708644752907 131080598023018062967129361)
      ·
        refine ⟨98310448517263547225347021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131080598023018062967129361 98310448517263547225347021)
        ·
          refine ⟨36866418193973830209505133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98310448517263547225347021 36866418193973830209505133)
          ·
            refine ⟨13824906822740186328564425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36866418193973830209505133 13824906822740186328564425)
            ·
              refine ⟨10368680117055139746423319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13824906822740186328564425 10368680117055139746423319)
              ·
                refine ⟨15553020175582709619634979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368680117055139746423319 15553020175582709619634979)
                ·
                  refine ⟨23329530263374064429452469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15553020175582709619634979 23329530263374064429452469)
                  ·
                    refine ⟨2187143462191318540261169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23329530263374064429452469 2187143462191318540261169)
                    ·
                      refine ⟨1640357596643488905195877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187143462191318540261169 1640357596643488905195877)
                      ·
                        rfl

theorem cell23_3194585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_3194585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194585 prefixEnd_3194585 := by exact prefixLift 3194585
  have htrace : WordTrace (prefixWord ++ tailWord_3194585) baseStart_3194585 baseEnd_3194585 := by
    simpa [prefixWord, tailWord_3194585, baseEnd_3194585] using wordTrace_append hprefix tailTrace_3194585
  have hstable : (prefixWord ++ tailWord_3194585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194585).length < 2 ^ (prefixWord ++ tailWord_3194585).sum := by decide
  have hdescent : baseEnd_3194585 < baseStart_3194585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194618 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_3194618 : Nat := 118140960795 + 3194618 * 2 ^ 59
def prefixEnd_3194618 : Nat := 4983230072969 + 3 ^ 40 * 3194618 * 2
def baseEnd_3194618 : Nat := 1640374541505087276083225

theorem tailTrace_3194618 : CollatzResearch.WordTrace tailWord_3194618 prefixEnd_3194618 1640374541505087276083225 := by
  unfold tailWord_3194618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129322685113014540572127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77678193826968038774859005 29129322685113014540572127)
  ·
    refine ⟨43693984027669521810858191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29129322685113014540572127 43693984027669521810858191)
    ·
      refine ⟨65540976041504282716287287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43693984027669521810858191 65540976041504282716287287)
      ·
        refine ⟨98311464062256424074430931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65540976041504282716287287 98311464062256424074430931)
        ·
          refine ⟨147467196093384636111646397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98311464062256424074430931 147467196093384636111646397)
          ·
            refine ⟨55300198535019238541867399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147467196093384636111646397 55300198535019238541867399)
            ·
              refine ⟨82950297802528857812801099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55300198535019238541867399 82950297802528857812801099)
              ·
                refine ⟨124425446703793286719201649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82950297802528857812801099 124425446703793286719201649)
                ·
                  refine ⟨93319085027844965039401237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124425446703793286719201649 93319085027844965039401237)
                  ·
                    refine ⟨4374332110680232736221933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93319085027844965039401237 4374332110680232736221933)
                    ·
                      refine ⟨1640374541505087276083225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374332110680232736221933 1640374541505087276083225)
                      ·
                        rfl

theorem cell23_3194618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_3194618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194618 prefixEnd_3194618 := by exact prefixLift 3194618
  have htrace : WordTrace (prefixWord ++ tailWord_3194618) baseStart_3194618 baseEnd_3194618 := by
    simpa [prefixWord, tailWord_3194618, baseEnd_3194618] using wordTrace_append hprefix tailTrace_3194618
  have hstable : (prefixWord ++ tailWord_3194618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194618).length < 2 ^ (prefixWord ++ tailWord_3194618).sum := by decide
  have hdescent : baseEnd_3194618 < baseStart_3194618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194630 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3194630 : Nat := 118140960795 + 3194630 * 2 ^ 59
def prefixEnd_3194630 : Nat := 4983230072969 + 3 ^ 40 * 3194630 * 2
def baseEnd_3194630 : Nat := 1640380703272941229133171

theorem tailTrace_3194630 : CollatzResearch.WordTrace tailWord_3194630 prefixEnd_3194630 1640380703272941229133171 := by
  unfold tailWord_3194630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641179013012768256616417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77678485610939056141150229 3641179013012768256616417)
  ·
    refine ⟨2730884259759576192462313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3641179013012768256616417 2730884259759576192462313)
    ·
      refine ⟨2048163194819682144346735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730884259759576192462313 2048163194819682144346735)
      ·
        refine ⟨3072244792229523216520103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048163194819682144346735 3072244792229523216520103)
        ·
          refine ⟨4608367188344284824780155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072244792229523216520103 4608367188344284824780155)
          ·
            refine ⟨6912550782516427237170233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608367188344284824780155 6912550782516427237170233)
            ·
              refine ⟨5184413086887320427877675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912550782516427237170233 5184413086887320427877675)
              ·
                refine ⟨7776619630330980641816513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184413086887320427877675 7776619630330980641816513)
                ·
                  refine ⟨5832464722748235481362385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7776619630330980641816513 5832464722748235481362385)
                  ·
                    refine ⟨4374348542061176611021789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832464722748235481362385 4374348542061176611021789)
                    ·
                      refine ⟨1640380703272941229133171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374348542061176611021789 1640380703272941229133171)
                      ·
                        rfl

theorem cell23_3194630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3194630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194630 prefixEnd_3194630 := by exact prefixLift 3194630
  have htrace : WordTrace (prefixWord ++ tailWord_3194630) baseStart_3194630 baseEnd_3194630 := by
    simpa [prefixWord, tailWord_3194630, baseEnd_3194630] using wordTrace_append hprefix tailTrace_3194630
  have hstable : (prefixWord ++ tailWord_3194630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194630).length < 2 ^ (prefixWord ++ tailWord_3194630).sum := by decide
  have hdescent : baseEnd_3194630 < baseStart_3194630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194632 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_3194632 : Nat := 118140960795 + 3194632 * 2 ^ 59
def prefixEnd_3194632 : Nat := 4983230072969 + 3 ^ 40 * 3194632 * 2
def baseEnd_3194632 : Nat := 1640381730234250221308161

theorem tailTrace_3194632 : CollatzResearch.WordTrace tailWord_3194632 prefixEnd_3194632 1640381730234250221308161 := by
  unfold tailWord_3194632
  simp only [CollatzResearch.WordTrace]
  refine ⟨58258900681200669276649075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77678534241600892368865433 58258900681200669276649075)
  ·
    refine ⟨87388351021801003914973613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58258900681200669276649075 87388351021801003914973613)
    ·
      refine ⟨32770631633175376468115105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87388351021801003914973613 32770631633175376468115105)
      ·
        refine ⟨24577973724881532351086329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32770631633175376468115105 24577973724881532351086329)
        ·
          refine ⟨18433480293661149263314747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24577973724881532351086329 18433480293661149263314747)
          ·
            refine ⟨27650220440491723894972121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18433480293661149263314747 27650220440491723894972121)
            ·
              refine ⟨20737665330368792921229091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27650220440491723894972121 20737665330368792921229091)
              ·
                refine ⟨31106497995553189381843637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737665330368792921229091 31106497995553189381843637)
                ·
                  refine ⟨2916234187083111504547841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31106497995553189381843637 2916234187083111504547841)
                  ·
                    refine ⟨2187175640312333628410881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916234187083111504547841 2187175640312333628410881)
                    ·
                      refine ⟨1640381730234250221308161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187175640312333628410881 1640381730234250221308161)
                      ·
                        rfl

theorem cell23_3194632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_3194632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194632 prefixEnd_3194632 := by exact prefixLift 3194632
  have htrace : WordTrace (prefixWord ++ tailWord_3194632) baseStart_3194632 baseEnd_3194632 := by
    simpa [prefixWord, tailWord_3194632, baseEnd_3194632] using wordTrace_append hprefix tailTrace_3194632
  have hstable : (prefixWord ++ tailWord_3194632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194632).length < 2 ^ (prefixWord ++ tailWord_3194632).sum := by decide
  have hdescent : baseEnd_3194632 < baseStart_3194632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194638 : List Nat := [4, 1, 1, 2, 1, 1, 4, 9]
def baseStart_3194638 : Nat := 118140960795 + 3194638 * 2 ^ 59
def prefixEnd_3194638 : Nat := 4983230072969 + 3 ^ 40 * 3194638 * 2
def baseEnd_3194638 : Nat := 60754993004376933253079

theorem tailTrace_3194638 : CollatzResearch.WordTrace tailWord_3194638 prefixEnd_3194638 60754993004376933253079 := by
  unfold tailWord_3194638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564752525047450197252071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77678680133586401052011045 14564752525047450197252071)
  ·
    refine ⟨21847128787571175295878107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14564752525047450197252071 21847128787571175295878107)
    ·
      refine ⟨32770693181356762943817161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21847128787571175295878107 32770693181356762943817161)
      ·
        refine ⟨24578019886017572207862871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32770693181356762943817161 24578019886017572207862871)
        ·
          refine ⟨36867029829026358311794307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24578019886017572207862871 36867029829026358311794307)
          ·
            refine ⟨55300544743539537467691461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36867029829026358311794307 55300544743539537467691461)
            ·
              refine ⟨10368852139413663275192149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55300544743539537467691461 10368852139413663275192149)
              ·
                refine ⟨60754993004376933253079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10368852139413663275192149 60754993004376933253079)
                ·
                  rfl

theorem cell23_3194638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_3194638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194638 prefixEnd_3194638 := by exact prefixLift 3194638
  have htrace : WordTrace (prefixWord ++ tailWord_3194638) baseStart_3194638 baseEnd_3194638 := by
    simpa [prefixWord, tailWord_3194638, baseEnd_3194638] using wordTrace_append hprefix tailTrace_3194638
  have hstable : (prefixWord ++ tailWord_3194638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194638).length < 2 ^ (prefixWord ++ tailWord_3194638).sum := by decide
  have hdescent : baseEnd_3194638 < baseStart_3194638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194642 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3194642 : Nat := 118140960795 + 3194642 * 2 ^ 59
def prefixEnd_3194642 : Nat := 4983230072969 + 3 ^ 40 * 3194642 * 2
def baseEnd_3194642 : Nat := 546795621680265060727705

theorem tailTrace_3194642 : CollatzResearch.WordTrace tailWord_3194642 prefixEnd_3194642 546795621680265060727705 := by
  unfold tailWord_3194642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129541523091277565290545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77678777394910073507441453 29129541523091277565290545)
  ·
    refine ⟨21847156142318458173967909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29129541523091277565290545 21847156142318458173967909)
    ·
      refine ⟨4096341776684710907618983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21847156142318458173967909 4096341776684710907618983)
      ·
        refine ⟨6144512665027066361428475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096341776684710907618983 6144512665027066361428475)
        ·
          refine ⟨9216768997540599542142713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144512665027066361428475 9216768997540599542142713)
          ·
            refine ⟨6912576748155449656607035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216768997540599542142713 6912576748155449656607035)
            ·
              refine ⟨10368865122233174484910553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912576748155449656607035 10368865122233174484910553)
              ·
                refine ⟨7776648841674880863682915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10368865122233174484910553 7776648841674880863682915)
                ·
                  refine ⟨11664973262512321295524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776648841674880863682915 11664973262512321295524373)
                  ·
                    refine ⟨546795621680265060727705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11664973262512321295524373 546795621680265060727705)
                    ·
                      rfl

theorem cell23_3194642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3194642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194642 prefixEnd_3194642 := by exact prefixLift 3194642
  have htrace : WordTrace (prefixWord ++ tailWord_3194642) baseStart_3194642 baseEnd_3194642 := by
    simpa [prefixWord, tailWord_3194642, baseEnd_3194642] using wordTrace_append hprefix tailTrace_3194642
  have hstable : (prefixWord ++ tailWord_3194642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194642).length < 2 ^ (prefixWord ++ tailWord_3194642).sum := by decide
  have hdescent : baseEnd_3194642 < baseStart_3194642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194645 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3194645 : Nat := 118140960795 + 3194645 * 2 ^ 59
def prefixEnd_3194645 : Nat := 4983230072969 + 3 ^ 40 * 3194645 * 2
def baseEnd_3194645 : Nat := 1640388405482758670445601

theorem tailTrace_3194645 : CollatzResearch.WordTrace tailWord_3194645 prefixEnd_3194645 1640388405482758670445601 := by
  unfold tailWord_3194645
  simp only [CollatzResearch.WordTrace]
  refine ⟨116518275511354241773521389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77678850340902827849014259 116518275511354241773521389)
  ·
    refine ⟨43694353316757840665070521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116518275511354241773521389 43694353316757840665070521)
    ·
      refine ⟨32770764987568380498802891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43694353316757840665070521 32770764987568380498802891)
      ·
        refine ⟨49156147481352570748204337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32770764987568380498802891 49156147481352570748204337)
        ·
          refine ⟨36867110611014428061153253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49156147481352570748204337 36867110611014428061153253)
          ·
            refine ⟨6912583239565205261466235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36867110611014428061153253 6912583239565205261466235)
            ·
              refine ⟨10368874859347807892199353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912583239565205261466235 10368874859347807892199353)
              ·
                refine ⟨7776656144510855919149515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10368874859347807892199353 7776656144510855919149515)
                ·
                  refine ⟨11664984216766283878724273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776656144510855919149515 11664984216766283878724273)
                  ·
                    refine ⟨8748738162574712909043205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11664984216766283878724273 8748738162574712909043205)
                    ·
                      refine ⟨1640388405482758670445601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8748738162574712909043205 1640388405482758670445601)
                      ·
                        rfl

theorem cell23_3194645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3194645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194645 prefixEnd_3194645 := by exact prefixLift 3194645
  have htrace : WordTrace (prefixWord ++ tailWord_3194645) baseStart_3194645 baseEnd_3194645 := by
    simpa [prefixWord, tailWord_3194645, baseEnd_3194645] using wordTrace_append hprefix tailTrace_3194645
  have hstable : (prefixWord ++ tailWord_3194645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194645).length < 2 ^ (prefixWord ++ tailWord_3194645).sum := by decide
  have hdescent : baseEnd_3194645 < baseStart_3194645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194668 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3194668 : Nat := 118140960795 + 3194668 * 2 ^ 59
def prefixEnd_3194668 : Nat := 4983230072969 + 3 ^ 40 * 3194668 * 2
def baseEnd_3194668 : Nat := 546800071845937360152665

theorem tailTrace_3194668 : CollatzResearch.WordTrace tailWord_3194668 prefixEnd_3194668 546800071845937360152665 := by
  unfold tailWord_3194668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58259557195135458350804329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77679409593513944467739105 58259557195135458350804329)
  ·
    refine ⟨43694667896351593763103247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58259557195135458350804329 43694667896351593763103247)
    ·
      refine ⟨65542001844527390644654871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43694667896351593763103247 65542001844527390644654871)
      ·
        refine ⟨98313002766791085966982307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65542001844527390644654871 98313002766791085966982307)
        ·
          refine ⟨147469504150186628950473461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98313002766791085966982307 147469504150186628950473461)
          ·
            refine ⟨13825266014079996464106887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147469504150186628950473461 13825266014079996464106887)
            ·
              refine ⟨20737899021119994696160331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825266014079996464106887 20737899021119994696160331)
              ·
                refine ⟨31106848531679992044240497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737899021119994696160331 31106848531679992044240497)
                ·
                  refine ⟨23330136398759994033180373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31106848531679992044240497 23330136398759994033180373)
                  ·
                    refine ⟨546800071845937360152665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23330136398759994033180373 546800071845937360152665)
                    ·
                      rfl

theorem cell23_3194668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3194668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194668 prefixEnd_3194668 := by exact prefixLift 3194668
  have htrace : WordTrace (prefixWord ++ tailWord_3194668) baseStart_3194668 baseEnd_3194668 := by
    simpa [prefixWord, tailWord_3194668, baseEnd_3194668] using wordTrace_append hprefix tailTrace_3194668
  have hstable : (prefixWord ++ tailWord_3194668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194668).length < 2 ^ (prefixWord ++ tailWord_3194668).sum := by decide
  have hdescent : baseEnd_3194668 < baseStart_3194668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194682 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_3194682 : Nat := 118140960795 + 3194682 * 2 ^ 59
def prefixEnd_3194682 : Nat := 4983230072969 + 3 ^ 40 * 3194682 * 2
def baseEnd_3194682 : Nat := 1640407404266975025682931

theorem tailTrace_3194682 : CollatzResearch.WordTrace tailWord_3194682 prefixEnd_3194682 1640407404266975025682931 := by
  unfold tailWord_3194682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129906253055049273154575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77679750008146798061745533 29129906253055049273154575)
  ·
    refine ⟨43694859379582573909731863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29129906253055049273154575 43694859379582573909731863)
    ·
      refine ⟨65542289069373860864597795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43694859379582573909731863 65542289069373860864597795)
      ·
        refine ⟨98313433604060791296896693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65542289069373860864597795 98313433604060791296896693)
        ·
          refine ⟨9216884400380699184084065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98313433604060791296896693 9216884400380699184084065)
          ·
            refine ⟨6912663300285524388063049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216884400380699184084065 6912663300285524388063049)
            ·
              refine ⟨5184497475214143291047287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912663300285524388063049 5184497475214143291047287)
              ·
                refine ⟨7776746212821214936570931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184497475214143291047287 7776746212821214936570931)
                ·
                  refine ⟨11665119319231822404856397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776746212821214936570931 11665119319231822404856397)
                  ·
                    refine ⟨4374419744711933401821149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11665119319231822404856397 4374419744711933401821149)
                    ·
                      refine ⟨1640407404266975025682931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374419744711933401821149 1640407404266975025682931)
                      ·
                        rfl

theorem cell23_3194682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_3194682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194682 prefixEnd_3194682 := by exact prefixLift 3194682
  have htrace : WordTrace (prefixWord ++ tailWord_3194682) baseStart_3194682 baseEnd_3194682 := by
    simpa [prefixWord, tailWord_3194682, baseEnd_3194682] using wordTrace_append hprefix tailTrace_3194682
  have hstable : (prefixWord ++ tailWord_3194682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194682).length < 2 ^ (prefixWord ++ tailWord_3194682).sum := by decide
  have hdescent : baseEnd_3194682 < baseStart_3194682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194698 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3194698 : Nat := 118140960795 + 3194698 * 2 ^ 59
def prefixEnd_3194698 : Nat := 4983230072969 + 3 ^ 40 * 3194698 * 2
def baseEnd_3194698 : Nat := 546805206652482321027619

theorem tailTrace_3194698 : CollatzResearch.WordTrace tailWord_3194698 prefixEnd_3194698 546805206652482321027619 := by
  unfold tailWord_3194698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130052145040557956300187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77680139053441487883467165 29130052145040557956300187)
  ·
    refine ⟨43695078217560836934450281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29130052145040557956300187 43695078217560836934450281)
    ·
      refine ⟨32771308663170627700837711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43695078217560836934450281 32771308663170627700837711)
      ·
        refine ⟨49156962994755941551256567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32771308663170627700837711 49156962994755941551256567)
        ·
          refine ⟨73735444492133912326884851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49156962994755941551256567 73735444492133912326884851)
          ·
            refine ⟨110603166738200868490327277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73735444492133912326884851 110603166738200868490327277)
            ·
              refine ⟨41476187526825325683872729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110603166738200868490327277 41476187526825325683872729)
              ·
                refine ⟨31107140645118994262904547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41476187526825325683872729 31107140645118994262904547)
                ·
                  refine ⟨46660710967678491394356821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31107140645118994262904547 46660710967678491394356821)
                  ·
                    refine ⟨546805206652482321027619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46660710967678491394356821 546805206652482321027619)
                    ·
                      rfl

theorem cell23_3194698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3194698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194698 prefixEnd_3194698 := by exact prefixLift 3194698
  have htrace : WordTrace (prefixWord ++ tailWord_3194698) baseStart_3194698 baseEnd_3194698 := by
    simpa [prefixWord, tailWord_3194698, baseEnd_3194698] using wordTrace_append hprefix tailTrace_3194698
  have hstable : (prefixWord ++ tailWord_3194698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194698).length < 2 ^ (prefixWord ++ tailWord_3194698).sum := by decide
  have hdescent : baseEnd_3194698 < baseStart_3194698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194709 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3194709 : Nat := 118140960795 + 3194709 * 2 ^ 59
def prefixEnd_3194709 : Nat := 4983230072969 + 3 ^ 40 * 3194709 * 2
def baseEnd_3194709 : Nat := 1640421268244646420045307

theorem tailTrace_3194709 : CollatzResearch.WordTrace tailWord_3194709 prefixEnd_3194709 1640421268244646420045307 := by
  unfold tailWord_3194709
  simp only [CollatzResearch.WordTrace]
  refine ⟨116520609783122380703851181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77680406522081587135900787 116520609783122380703851181)
  ·
    refine ⟨43695228668670892763944193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116520609783122380703851181 43695228668670892763944193)
    ·
      refine ⟨32771421501503169572958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43695228668670892763944193 32771421501503169572958145)
      ·
        refine ⟨24578566126127377179718609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32771421501503169572958145 24578566126127377179718609)
        ·
          refine ⟨18433924594595532884788957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24578566126127377179718609 18433924594595532884788957)
          ·
            refine ⟨6912721722973324831795859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18433924594595532884788957 6912721722973324831795859)
            ·
              refine ⟨10369082584459987247693789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912721722973324831795859 10369082584459987247693789)
              ·
                refine ⟨3888405969172495217885171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10369082584459987247693789 3888405969172495217885171)
                ·
                  refine ⟨5832608953758742826827757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888405969172495217885171 5832608953758742826827757)
                  ·
                    refine ⟨2187228357659528560060409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5832608953758742826827757 2187228357659528560060409)
                    ·
                      refine ⟨1640421268244646420045307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187228357659528560060409 1640421268244646420045307)
                      ·
                        rfl

theorem cell23_3194709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3194709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194709 prefixEnd_3194709 := by exact prefixLift 3194709
  have htrace : WordTrace (prefixWord ++ tailWord_3194709) baseStart_3194709 baseEnd_3194709 := by
    simpa [prefixWord, tailWord_3194709, baseEnd_3194709] using wordTrace_append hprefix tailTrace_3194709
  have hstable : (prefixWord ++ tailWord_3194709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194709).length < 2 ^ (prefixWord ++ tailWord_3194709).sum := by decide
  have hdescent : baseEnd_3194709 < baseStart_3194709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194775 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 4, 5]
def baseStart_3194775 : Nat := 118140960795 + 3194775 * 2 ^ 59
def prefixEnd_3194775 : Nat := 4983230072969 + 3 ^ 40 * 3194775 * 2
def baseEnd_3194775 : Nat := 546818385989281053940001

theorem tailTrace_3194775 : CollatzResearch.WordTrace tailWord_3194775 prefixEnd_3194775 546818385989281053940001 := by
  unfold tailWord_3194775
  simp only [CollatzResearch.WordTrace]
  refine ⟨116523017000883273975753779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77682011333922182650502519 116523017000883273975753779)
  ·
    refine ⟨174784525501324910963630669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116523017000883273975753779 174784525501324910963630669)
    ·
      refine ⟨65544197062996841611361501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174784525501324910963630669 65544197062996841611361501)
      ·
        refine ⟨24579073898623815604260563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65544197062996841611361501 24579073898623815604260563)
        ·
          refine ⟨36868610847935723406390845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24579073898623815604260563 36868610847935723406390845)
          ·
            refine ⟨13825729067975896277396567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36868610847935723406390845 13825729067975896277396567)
            ·
              refine ⟨20738593601963844416094851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825729067975896277396567 20738593601963844416094851)
              ·
                refine ⟨31107890402945766624142277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20738593601963844416094851 31107890402945766624142277)
                ·
                  refine ⟨5832729450552331242026677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31107890402945766624142277 5832729450552331242026677)
                  ·
                    refine ⟨546818385989281053940001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5832729450552331242026677 546818385989281053940001)
                    ·
                      rfl

theorem cell23_3194775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_3194775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194775 prefixEnd_3194775 := by exact prefixLift 3194775
  have htrace : WordTrace (prefixWord ++ tailWord_3194775) baseStart_3194775 baseEnd_3194775 := by
    simpa [prefixWord, tailWord_3194775, baseEnd_3194775] using wordTrace_append hprefix tailTrace_3194775
  have hstable : (prefixWord ++ tailWord_3194775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194775).length < 2 ^ (prefixWord ++ tailWord_3194775).sum := by decide
  have hdescent : baseEnd_3194775 < baseStart_3194775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194832 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_3194832 : Nat := 118140960795 + 3194832 * 2 ^ 59
def prefixEnd_3194832 : Nat := 4983230072969 + 3 ^ 40 * 3194832 * 2
def baseEnd_3194832 : Nat := 1640484426365149438807241

theorem tailTrace_3194832 : CollatzResearch.WordTrace tailWord_3194832 prefixEnd_3194832 1640484426365149438807241 := by
  unfold tailWord_3194832
  simp only [CollatzResearch.WordTrace]
  refine ⟨58262547980838386355289375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77683397307784515140385833 58262547980838386355289375)
  ·
    refine ⟨87393821971257579532934063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58262547980838386355289375 87393821971257579532934063)
    ·
      refine ⟨131090732956886369299401095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87393821971257579532934063 131090732956886369299401095)
      ·
        refine ⟨196636099435329553949101643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131090732956886369299401095 196636099435329553949101643)
        ·
          refine ⟨294954149152994330923652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196636099435329553949101643 294954149152994330923652465)
          ·
            refine ⟨221215611864745748192739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294954149152994330923652465 221215611864745748192739349)
            ·
              refine ⟨10369481806159956946534657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221215611864745748192739349 10369481806159956946534657)
              ·
                refine ⟨7777111354619967709900993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10369481806159956946534657 7777111354619967709900993)
                ·
                  refine ⟨5832833515964975782425745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7777111354619967709900993 5832833515964975782425745)
                  ·
                    refine ⟨4374625136973731836819309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832833515964975782425745 4374625136973731836819309)
                    ·
                      refine ⟨1640484426365149438807241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374625136973731836819309 1640484426365149438807241)
                      ·
                        rfl

theorem cell23_3194832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_3194832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194832 prefixEnd_3194832 := by exact prefixLift 3194832
  have htrace : WordTrace (prefixWord ++ tailWord_3194832) baseStart_3194832 baseEnd_3194832 := by
    simpa [prefixWord, tailWord_3194832, baseEnd_3194832] using wordTrace_append hprefix tailTrace_3194832
  have hstable : (prefixWord ++ tailWord_3194832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194832).length < 2 ^ (prefixWord ++ tailWord_3194832).sum := by decide
  have hdescent : baseEnd_3194832 < baseStart_3194832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194839 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 1, 4]
def baseStart_3194839 : Nat := 118140960795 + 3194839 * 2 ^ 59
def prefixEnd_3194839 : Nat := 4983230072969 + 3 ^ 40 * 3194839 * 2
def baseEnd_3194839 : Nat := 546829340243243637139903

theorem tailTrace_3194839 : CollatzResearch.WordTrace tailWord_3194839 prefixEnd_3194839 546829340243243637139903 := by
  unfold tailWord_3194839
  simp only [CollatzResearch.WordTrace]
  refine ⟨116525351272651412906083571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77683567515100941937389047 116525351272651412906083571)
  ·
    refine ⟨174788026908977119359125357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116525351272651412906083571 174788026908977119359125357)
    ·
      refine ⟨65545510090866419759672009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174788026908977119359125357 65545510090866419759672009)
      ·
        refine ⟨49159132568149814819754007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65545510090866419759672009 49159132568149814819754007)
        ·
          refine ⟨73738698852224722229631011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49159132568149814819754007 73738698852224722229631011)
          ·
            refine ⟨110608048278337083344446517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73738698852224722229631011 110608048278337083344446517)
            ·
              refine ⟨10369504526094101563541861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110608048278337083344446517 10369504526094101563541861)
              ·
                refine ⟨1944282098642644043164099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10369504526094101563541861 1944282098642644043164099)
                ·
                  refine ⟨2916423147963966064746149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944282098642644043164099 2916423147963966064746149)
                  ·
                    refine ⟨546829340243243637139903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2916423147963966064746149 546829340243243637139903)
                    ·
                      rfl

theorem cell23_3194839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_3194839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194839 prefixEnd_3194839 := by exact prefixLift 3194839
  have htrace : WordTrace (prefixWord ++ tailWord_3194839) baseStart_3194839 baseEnd_3194839 := by
    simpa [prefixWord, tailWord_3194839, baseEnd_3194839] using wordTrace_append hprefix tailTrace_3194839
  have hstable : (prefixWord ++ tailWord_3194839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194839).length < 2 ^ (prefixWord ++ tailWord_3194839).sum := by decide
  have hdescent : baseEnd_3194839 < baseStart_3194839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194916 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_3194916 : Nat := 118140960795 + 3194916 * 2 ^ 59
def prefixEnd_3194916 : Nat := 4983230072969 + 3 ^ 40 * 3194916 * 2
def baseEnd_3194916 : Nat := 546842519580042370052285

theorem tailTrace_3194916 : CollatzResearch.WordTrace tailWord_3194916 prefixEnd_3194916 546842519580042370052285 := by
  unfold tailWord_3194916
  simp only [CollatzResearch.WordTrace]
  refine ⟨58264079846686227528318301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77685439795581636704424401 58264079846686227528318301)
  ·
    refine ⟨21849029942507335323119363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58264079846686227528318301 21849029942507335323119363)
    ·
      refine ⟨32773544913761002984679045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21849029942507335323119363 32773544913761002984679045)
      ·
        refine ⟨6145039671330188059627321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32773544913761002984679045 6145039671330188059627321)
        ·
          refine ⟨4608779753497641044720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145039671330188059627321 4608779753497641044720491)
          ·
            refine ⟨6913169630246461567080737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608779753497641044720491 6913169630246461567080737)
            ·
              refine ⟨5184877222684846175310553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913169630246461567080737 5184877222684846175310553)
              ·
                refine ⟨3888657917013634631482915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184877222684846175310553 3888657917013634631482915)
                ·
                  refine ⟨5832986875520451947224373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888657917013634631482915 5832986875520451947224373)
                  ·
                    refine ⟨546842519580042370052285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5832986875520451947224373 546842519580042370052285)
                    ·
                      rfl

theorem cell23_3194916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_3194916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194916 prefixEnd_3194916 := by exact prefixLift 3194916
  have htrace : WordTrace (prefixWord ++ tailWord_3194916) baseStart_3194916 baseEnd_3194916 := by
    simpa [prefixWord, tailWord_3194916, baseEnd_3194916] using wordTrace_append hprefix tailTrace_3194916
  have hstable : (prefixWord ++ tailWord_3194916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194916).length < 2 ^ (prefixWord ++ tailWord_3194916).sum := by decide
  have hdescent : baseEnd_3194916 < baseStart_3194916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194952 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3194952 : Nat := 118140960795 + 3194952 * 2 ^ 59
def prefixEnd_3194952 : Nat := 4983230072969 + 3 ^ 40 * 3194952 * 2
def baseEnd_3194952 : Nat := 1640546044043688969306689

theorem tailTrace_3194952 : CollatzResearch.WordTrace tailWord_3194952 prefixEnd_3194952 1640546044043688969306689 := by
  unfold tailWord_3194952
  simp only [CollatzResearch.WordTrace]
  refine ⟨58264736360621016602473555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77686315147494688803298073 58264736360621016602473555)
  ·
    refine ⟨87397104540931524903710333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58264736360621016602473555 87397104540931524903710333)
    ·
      refine ⟨32773914202849321838891375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87397104540931524903710333 32773914202849321838891375)
      ·
        refine ⟨49160871304273982758337063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32773914202849321838891375 49160871304273982758337063)
        ·
          refine ⟨73741306956410974137505595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49160871304273982758337063 73741306956410974137505595)
          ·
            refine ⟨110611960434616461206258393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73741306956410974137505595 110611960434616461206258393)
            ·
              refine ⟨82958970325962345904693795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110611960434616461206258393 82958970325962345904693795)
              ·
                refine ⟨124438455488943518857040693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82958970325962345904693795 124438455488943518857040693)
                ·
                  refine ⟨11666105202088454892847565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124438455488943518857040693 11666105202088454892847565)
                  ·
                    refine ⟨4374789450783170584817837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11666105202088454892847565 4374789450783170584817837)
                    ·
                      refine ⟨1640546044043688969306689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374789450783170584817837 1640546044043688969306689)
                      ·
                        rfl

theorem cell23_3194952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3194952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194952 prefixEnd_3194952 := by exact prefixLift 3194952
  have htrace : WordTrace (prefixWord ++ tailWord_3194952) baseStart_3194952 baseEnd_3194952 := by
    simpa [prefixWord, tailWord_3194952, baseEnd_3194952] using wordTrace_append hprefix tailTrace_3194952
  have hstable : (prefixWord ++ tailWord_3194952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194952).length < 2 ^ (prefixWord ++ tailWord_3194952).sum := by decide
  have hdescent : baseEnd_3194952 < baseStart_3194952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194955 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 9]
def baseStart_3194955 : Nat := 118140960795 + 3194955 * 2 ^ 59
def prefixEnd_3194955 : Nat := 4983230072969 + 3 ^ 40 * 3194955 * 2
def baseEnd_3194955 : Nat := 546849194828550819189725

theorem tailTrace_3194955 : CollatzResearch.WordTrace tailWord_3194955 prefixEnd_3194955 546849194828550819189725 := by
  unfold tailWord_3194955
  simp only [CollatzResearch.WordTrace]
  refine ⟨116529582140231164717306319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77686388093487443144870879 116529582140231164717306319)
  ·
    refine ⟨174794373210346747075959479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116529582140231164717306319 174794373210346747075959479)
    ·
      refine ⟨262191559815520120613939219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174794373210346747075959479 262191559815520120613939219)
      ·
        refine ⟨393287339723280180920908829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262191559815520120613939219 393287339723280180920908829)
        ·
          refine ⟨147482752396230067845340811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393287339723280180920908829 147482752396230067845340811)
          ·
            refine ⟨221224128594345101768011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147482752396230067845340811 221224128594345101768011217)
            ·
              refine ⟨165918096445758826326008413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221224128594345101768011217 165918096445758826326008413)
              ·
                refine ⟨62219286167159559872253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165918096445758826326008413 62219286167159559872253155)
                ·
                  refine ⟨93328929250739339808379733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62219286167159559872253155 93328929250739339808379733)
                  ·
                    refine ⟨546849194828550819189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 93328929250739339808379733 546849194828550819189725)
                    ·
                      rfl

theorem cell23_3194955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_3194955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194955 prefixEnd_3194955 := by exact prefixLift 3194955
  have htrace : WordTrace (prefixWord ++ tailWord_3194955) baseStart_3194955 baseEnd_3194955 := by
    simpa [prefixWord, tailWord_3194955, baseEnd_3194955] using wordTrace_append hprefix tailTrace_3194955
  have hstable : (prefixWord ++ tailWord_3194955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194955).length < 2 ^ (prefixWord ++ tailWord_3194955).sum := by decide
  have hdescent : baseEnd_3194955 < baseStart_3194955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194966 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3194966 : Nat := 118140960795 + 3194966 * 2 ^ 59
def prefixEnd_3194966 : Nat := 4983230072969 + 3 ^ 40 * 3194966 * 2
def baseEnd_3194966 : Nat := 1640553232772851914531625

theorem tailTrace_3194966 : CollatzResearch.WordTrace tailWord_3194966 prefixEnd_3194966 1640553232772851914531625 := by
  unfold tailWord_3194966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283123958949457099747297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77686655562127542397304501 7283123958949457099747297)
  ·
    refine ⟨5462342969212092824810473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7283123958949457099747297 5462342969212092824810473)
    ·
      refine ⟨4096757226909069618607855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5462342969212092824810473 4096757226909069618607855)
      ·
        refine ⟨6145135840363604427911783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096757226909069618607855 6145135840363604427911783)
        ·
          refine ⟨9217703760545406641867675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145135840363604427911783 9217703760545406641867675)
          ·
            refine ⟨13826555640818109962801513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217703760545406641867675 13826555640818109962801513)
            ·
              refine ⟨10369916730613582472101135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13826555640818109962801513 10369916730613582472101135)
              ·
                refine ⟨15554875095920373708151703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10369916730613582472101135 15554875095920373708151703)
                ·
                  refine ⟨23332312643880560562227555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15554875095920373708151703 23332312643880560562227555)
                  ·
                    refine ⟨34998468965820840843341333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23332312643880560562227555 34998468965820840843341333)
                    ·
                      refine ⟨1640553232772851914531625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34998468965820840843341333 1640553232772851914531625)
                      ·
                        rfl

theorem cell23_3194966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3194966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194966 prefixEnd_3194966 := by exact prefixLift 3194966
  have htrace : WordTrace (prefixWord ++ tailWord_3194966) baseStart_3194966 baseEnd_3194966 := by
    simpa [prefixWord, tailWord_3194966, baseEnd_3194966] using wordTrace_append hprefix tailTrace_3194966
  have hstable : (prefixWord ++ tailWord_3194966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194966).length < 2 ^ (prefixWord ++ tailWord_3194966).sum := by decide
  have hdescent : baseEnd_3194966 < baseStart_3194966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194973 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3194973 : Nat := 118140960795 + 3194973 * 2 ^ 59
def prefixEnd_3194973 : Nat := 4983230072969 + 3 ^ 40 * 3194973 * 2
def baseEnd_3194973 : Nat := 1640556827137433387144093

theorem tailTrace_3194973 : CollatzResearch.WordTrace tailWord_3194973 prefixEnd_3194973 1640556827137433387144093 := by
  unfold tailWord_3194973
  simp only [CollatzResearch.WordTrace]
  refine ⟨116530238654165953791461573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77686825769443969194307715 116530238654165953791461573)
  ·
    refine ⟨21849419747656116335899045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116530238654165953791461573 21849419747656116335899045)
    ·
      refine ⟨4096766202685521812981071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21849419747656116335899045 4096766202685521812981071)
      ·
        refine ⟨6145149304028282719471607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096766202685521812981071 6145149304028282719471607)
        ·
          refine ⟨9217723956042424079207411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145149304028282719471607 9217723956042424079207411)
          ·
            refine ⟨13826585934063636118811117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217723956042424079207411 13826585934063636118811117)
            ·
              refine ⟨5184969725273863544554169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13826585934063636118811117 5184969725273863544554169)
              ·
                refine ⟨3888727293955397658415627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184969725273863544554169 3888727293955397658415627)
                ·
                  refine ⟨5833090940933096487623441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888727293955397658415627 5833090940933096487623441)
                  ·
                    refine ⟨4374818205699822365717581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833090940933096487623441 4374818205699822365717581)
                    ·
                      refine ⟨1640556827137433387144093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374818205699822365717581 1640556827137433387144093)
                      ·
                        rfl

theorem cell23_3194973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3194973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194973 prefixEnd_3194973 := by exact prefixLift 3194973
  have htrace : WordTrace (prefixWord ++ tailWord_3194973) baseStart_3194973 baseEnd_3194973 := by
    simpa [prefixWord, tailWord_3194973, baseEnd_3194973] using wordTrace_append hprefix tailTrace_3194973
  have hstable : (prefixWord ++ tailWord_3194973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194973).length < 2 ^ (prefixWord ++ tailWord_3194973).sum := by decide
  have hdescent : baseEnd_3194973 < baseStart_3194973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194986 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3194986 : Nat := 118140960795 + 3194986 * 2 ^ 59
def prefixEnd_3194986 : Nat := 4983230072969 + 3 ^ 40 * 3194986 * 2
def baseEnd_3194986 : Nat := 1640563502385941836281533

theorem tailTrace_3194986 : CollatzResearch.WordTrace tailWord_3194986 prefixEnd_3194986 1640563502385941836281533 := by
  unfold tailWord_3194986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132678200779714252921203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77687141868745904674456541 29132678200779714252921203)
  ·
    refine ⟨43699017301169571379381805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29132678200779714252921203 43699017301169571379381805)
    ·
      refine ⟨16387131487938589267268177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43699017301169571379381805 16387131487938589267268177)
      ·
        refine ⟨12290348615953941950451133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16387131487938589267268177 12290348615953941950451133)
        ·
          refine ⟨4608880730982728231419175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12290348615953941950451133 4608880730982728231419175)
          ·
            refine ⟨6913321096474092347128763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608880730982728231419175 6913321096474092347128763)
            ·
              refine ⟨10369981644711138520693145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913321096474092347128763 10369981644711138520693145)
              ·
                refine ⟨7777486233533353890519859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10369981644711138520693145 7777486233533353890519859)
                ·
                  refine ⟨11666229350300030835779789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7777486233533353890519859 11666229350300030835779789)
                  ·
                    refine ⟨4374836006362511563417421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11666229350300030835779789 4374836006362511563417421)
                    ·
                      refine ⟨1640563502385941836281533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374836006362511563417421 1640563502385941836281533)
                      ·
                        rfl

theorem cell23_3194986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3194986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3194986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3194986 prefixEnd_3194986 := by exact prefixLift 3194986
  have htrace : WordTrace (prefixWord ++ tailWord_3194986) baseStart_3194986 baseEnd_3194986 := by
    simpa [prefixWord, tailWord_3194986, baseEnd_3194986] using wordTrace_append hprefix tailTrace_3194986
  have hstable : (prefixWord ++ tailWord_3194986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194986).length < 2 ^ (prefixWord ++ tailWord_3194986).sum := by decide
  have hdescent : baseEnd_3194986 < baseStart_3194986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195047 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3195047 : Nat := 118140960795 + 3195047 * 2 ^ 59
def prefixEnd_3195047 : Nat := 4983230072969 + 3 ^ 40 * 3195047 * 2
def baseEnd_3195047 : Nat := 1640594824705866097618753

theorem tailTrace_3195047 : CollatzResearch.WordTrace tailWord_3195047 prefixEnd_3195047 1640594824705866097618753 := by
  unfold tailWord_3195047
  simp only [CollatzResearch.WordTrace]
  refine ⟨116532937655897864429655395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77688625103931909619770263 116532937655897864429655395)
  ·
    refine ⟨174799406483846796644483093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116532937655897864429655395 174799406483846796644483093)
    ·
      refine ⟨8193722178930318592710145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174799406483846796644483093 8193722178930318592710145)
      ·
        refine ⟨6145291634197738944532609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8193722178930318592710145 6145291634197738944532609)
        ·
          refine ⟨4608968725648304208399457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145291634197738944532609 4608968725648304208399457)
          ·
            refine ⟨3456726544236228156299593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608968725648304208399457 3456726544236228156299593)
            ·
              refine ⟨2592544908177171117224695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456726544236228156299593 2592544908177171117224695)
              ·
                refine ⟨3888817362265756675837043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592544908177171117224695 3888817362265756675837043)
                ·
                  refine ⟨5833226043398635013755565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888817362265756675837043 5833226043398635013755565)
                  ·
                    refine ⟨2187459766274488130158337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5833226043398635013755565 2187459766274488130158337)
                    ·
                      refine ⟨1640594824705866097618753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187459766274488130158337 1640594824705866097618753)
                      ·
                        rfl

theorem cell23_3195047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3195047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195047 prefixEnd_3195047 := by exact prefixLift 3195047
  have htrace : WordTrace (prefixWord ++ tailWord_3195047) baseStart_3195047 baseEnd_3195047 := by
    simpa [prefixWord, tailWord_3195047, baseEnd_3195047] using wordTrace_append hprefix tailTrace_3195047
  have hstable : (prefixWord ++ tailWord_3195047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195047).length < 2 ^ (prefixWord ++ tailWord_3195047).sum := by decide
  have hdescent : baseEnd_3195047 < baseStart_3195047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195054 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3195054 : Nat := 118140960795 + 3195054 * 2 ^ 59
def prefixEnd_3195054 : Nat := 4983230072969 + 3 ^ 40 * 3195054 * 2
def baseEnd_3195054 : Nat := 1640598419070447570231221

theorem tailTrace_3195054 : CollatzResearch.WordTrace tailWord_3195054 prefixEnd_3195054 1640598419070447570231221 := by
  unfold tailWord_3195054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14566649120859063078145027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77688795311248336416773477 14566649120859063078145027)
  ·
    refine ⟨21849973681288594617217541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14566649120859063078145027 21849973681288594617217541)
    ·
      refine ⟨4096870065241611490728289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21849973681288594617217541 4096870065241611490728289)
      ·
        refine ⟨3072652548931208618046217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096870065241611490728289 3072652548931208618046217)
        ·
          refine ⟨2304489411698406463534663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3072652548931208618046217 2304489411698406463534663)
          ·
            refine ⟨3456734117547609695301995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304489411698406463534663 3456734117547609695301995)
            ·
              refine ⟨5185101176321414542952993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456734117547609695301995 5185101176321414542952993)
              ·
                refine ⟨3888825882241060907214745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185101176321414542952993 3888825882241060907214745)
                ·
                  refine ⟨2916619411680795680411059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3888825882241060907214745 2916619411680795680411059)
                  ·
                    refine ⟨4374929117521193520616589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2916619411680795680411059 4374929117521193520616589)
                    ·
                      refine ⟨1640598419070447570231221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374929117521193520616589 1640598419070447570231221)
                      ·
                        rfl

theorem cell23_3195054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3195054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195054 prefixEnd_3195054 := by exact prefixLift 3195054
  have htrace : WordTrace (prefixWord ++ tailWord_3195054) baseStart_3195054 baseEnd_3195054 := by
    simpa [prefixWord, tailWord_3195054, baseEnd_3195054] using wordTrace_append hprefix tailTrace_3195054
  have hstable : (prefixWord ++ tailWord_3195054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195054).length < 2 ^ (prefixWord ++ tailWord_3195054).sum := by decide
  have hdescent : baseEnd_3195054 < baseStart_3195054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195076 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3195076 : Nat := 118140960795 + 3195076 * 2 ^ 59
def prefixEnd_3195076 : Nat := 4983230072969 + 3 ^ 40 * 3195076 * 2
def baseEnd_3195076 : Nat := 1640609715644846484156119

theorem tailTrace_3195076 : CollatzResearch.WordTrace tailWord_3195076 prefixEnd_3195076 1640609715644846484156119 := by
  unfold tailWord_3195076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58266997686396401191230541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77689330248528534921640721 58266997686396401191230541)
  ·
    refine ⟨21850124132398650446711453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58266997686396401191230541 21850124132398650446711453)
    ·
      refine ⟨8193796549649493917516795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21850124132398650446711453 8193796549649493917516795)
      ·
        refine ⟨12290694824474240876275193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8193796549649493917516795 12290694824474240876275193)
        ·
          refine ⟨9218021118355680657206395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12290694824474240876275193 9218021118355680657206395)
          ·
            refine ⟨13827031677533520985809593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218021118355680657206395 13827031677533520985809593)
            ·
              refine ⟨10370273758150140739357195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13827031677533520985809593 10370273758150140739357195)
              ·
                refine ⟨15555410637225211109035793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370273758150140739357195 15555410637225211109035793)
                ·
                  refine ⟨11666557977918908331776845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15555410637225211109035793 11666557977918908331776845)
                  ·
                    refine ⟨4374959241719590624416317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11666557977918908331776845 4374959241719590624416317)
                    ·
                      refine ⟨1640609715644846484156119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4374959241719590624416317 1640609715644846484156119)
                      ·
                        rfl

theorem cell23_3195076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3195076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195076 prefixEnd_3195076 := by exact prefixLift 3195076
  have htrace : WordTrace (prefixWord ++ tailWord_3195076) baseStart_3195076 baseEnd_3195076 := by
    simpa [prefixWord, tailWord_3195076, baseEnd_3195076] using wordTrace_append hprefix tailTrace_3195076
  have hstable : (prefixWord ++ tailWord_3195076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195076).length < 2 ^ (prefixWord ++ tailWord_3195076).sum := by decide
  have hdescent : baseEnd_3195076 < baseStart_3195076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195099 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 6, 2]
def baseStart_3195099 : Nat := 118140960795 + 3195099 * 2 ^ 59
def prefixEnd_3195099 : Nat := 4983230072969 + 3 ^ 40 * 3195099 * 2
def baseEnd_3195099 : Nat := 1640621525699899894168513

theorem tailTrace_3195099 : CollatzResearch.WordTrace tailWord_3195099 prefixEnd_3195099 1640621525699899894168513 := by
  unfold tailWord_3195099
  simp only [CollatzResearch.WordTrace]
  refine ⟨116534834251709477310548351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77689889501139651540365567 116534834251709477310548351)
  ·
    refine ⟨174802251377564215965822527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116534834251709477310548351 174802251377564215965822527)
    ·
      refine ⟨262203377066346323948733791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174802251377564215965822527 262203377066346323948733791)
      ·
        refine ⟨393305065599519485923100687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262203377066346323948733791 393305065599519485923100687)
        ·
          refine ⟨589957598399279228884651031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393305065599519485923100687 589957598399279228884651031)
          ·
            refine ⟨884936397598918843326976547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589957598399279228884651031 884936397598918843326976547)
            ·
              refine ⟨1327404596398378264990464821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884936397598918843326976547 1327404596398378264990464821)
              ·
                refine ⟨124444180912347962342856077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327404596398378264990464821 124444180912347962342856077)
                ·
                  refine ⟨46666567842130485878571029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124444180912347962342856077 46666567842130485878571029)
                  ·
                    refine ⟨2187495367599866525558017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46666567842130485878571029 2187495367599866525558017)
                    ·
                      refine ⟨1640621525699899894168513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187495367599866525558017 1640621525699899894168513)
                      ·
                        rfl

theorem cell23_3195099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6, 2].length) (baseStart_3195099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195099 prefixEnd_3195099 := by exact prefixLift 3195099
  have htrace : WordTrace (prefixWord ++ tailWord_3195099) baseStart_3195099 baseEnd_3195099 := by
    simpa [prefixWord, tailWord_3195099, baseEnd_3195099] using wordTrace_append hprefix tailTrace_3195099
  have hstable : (prefixWord ++ tailWord_3195099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195099).length < 2 ^ (prefixWord ++ tailWord_3195099).sum := by decide
  have hdescent : baseEnd_3195099 < baseStart_3195099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195139 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 6]
def baseStart_3195139 : Nat := 118140960795 + 3195139 * 2 ^ 59
def prefixEnd_3195139 : Nat := 4983230072969 + 3 ^ 40 * 3195139 * 2
def baseEnd_3195139 : Nat := 182293562769564415296481

theorem tailTrace_3195139 : CollatzResearch.WordTrace tailWord_3195139 prefixEnd_3195139 182293562769564415296481 := by
  unfold tailWord_3195139
  simp only [CollatzResearch.WordTrace]
  refine ⟨116536293171564564142004471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77690862114376376094669647 116536293171564564142004471)
  ·
    refine ⟨174804439757346846213006707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116536293171564564142004471 174804439757346846213006707)
    ·
      refine ⟨262206659636020269319510061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174804439757346846213006707 262206659636020269319510061)
      ·
        refine ⟨98327497363507600994816273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262206659636020269319510061 98327497363507600994816273)
        ·
          refine ⟨73745623022630700746112205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98327497363507600994816273 73745623022630700746112205)
          ·
            refine ⟨27654608633486512779792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73745623022630700746112205 27654608633486512779792077)
            ·
              refine ⟨10370478237557442292422029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27654608633486512779792077 10370478237557442292422029)
              ·
                refine ⟨3888929339084040859658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10370478237557442292422029 3888929339084040859658261)
                ·
                  refine ⟨182293562769564415296481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3888929339084040859658261 182293562769564415296481)
                  ·
                    rfl

theorem cell23_3195139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 6].length) (baseStart_3195139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195139 prefixEnd_3195139 := by exact prefixLift 3195139
  have htrace : WordTrace (prefixWord ++ tailWord_3195139) baseStart_3195139 baseEnd_3195139 := by
    simpa [prefixWord, tailWord_3195139, baseEnd_3195139] using wordTrace_append hprefix tailTrace_3195139
  have hstable : (prefixWord ++ tailWord_3195139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195139).length < 2 ^ (prefixWord ++ tailWord_3195139).sum := by decide
  have hdescent : baseEnd_3195139 < baseStart_3195139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195219 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_3195219 : Nat := 118140960795 + 3195219 * 2 ^ 59
def prefixEnd_3195219 : Nat := 4983230072969 + 3 ^ 40 * 3195219 * 2
def baseEnd_3195219 : Nat := 1640683143378439424667961

theorem tailTrace_3195219 : CollatzResearch.WordTrace tailWord_3195219 prefixEnd_3195219 1640683143378439424667961 := by
  unfold tailWord_3195219
  simp only [CollatzResearch.WordTrace]
  refine ⟨116539211011274737804916711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77692807340849825203277807 116539211011274737804916711)
  ·
    refine ⟨174808816516912106707375067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116539211011274737804916711 174808816516912106707375067)
    ·
      refine ⟨262213224775368160061062601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174808816516912106707375067 262213224775368160061062601)
      ·
        refine ⟨196659918581526120045796951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262213224775368160061062601 196659918581526120045796951)
        ·
          refine ⟨294989877872289180068695427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196659918581526120045796951 294989877872289180068695427)
          ·
            refine ⟨442484816808433770103043141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294989877872289180068695427 442484816808433770103043141)
            ·
              refine ⟨82965903151581331894320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442484816808433770103043141 82965903151581331894320589)
              ·
                refine ⟨31112213681842999460370221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82965903151581331894320589 31112213681842999460370221)
                ·
                  refine ⟨11667080130691124797638833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31112213681842999460370221 11667080130691124797638833)
                  ·
                    refine ⟨8750310098018343598229125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11667080130691124797638833 8750310098018343598229125)
                    ·
                      refine ⟨1640683143378439424667961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8750310098018343598229125 1640683143378439424667961)
                      ·
                        rfl

theorem cell23_3195219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_3195219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195219 prefixEnd_3195219 := by exact prefixLift 3195219
  have htrace : WordTrace (prefixWord ++ tailWord_3195219) baseStart_3195219 baseEnd_3195219 := by
    simpa [prefixWord, tailWord_3195219, baseEnd_3195219] using wordTrace_append hprefix tailTrace_3195219
  have hstable : (prefixWord ++ tailWord_3195219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195219).length < 2 ^ (prefixWord ++ tailWord_3195219).sum := by decide
  have hdescent : baseEnd_3195219 < baseStart_3195219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195220 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3195220 : Nat := 118140960795 + 3195220 * 2 ^ 59
def prefixEnd_3195220 : Nat := 4983230072969 + 3 ^ 40 * 3195220 * 2
def baseEnd_3195220 : Nat := 546894552286364640251819

theorem tailTrace_3195220 : CollatzResearch.WordTrace tailWord_3195220 prefixEnd_3195220 546894552286364640251819 := by
  unfold tailWord_3195220
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269623742135557487851557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77692831656180743317135409 58269623742135557487851557)
  ·
    refine ⟨10925554451650417028972167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58269623742135557487851557 10925554451650417028972167)
    ·
      refine ⟨16388331677475625543458251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10925554451650417028972167 16388331677475625543458251)
      ·
        refine ⟨24582497516213438315187377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16388331677475625543458251 24582497516213438315187377)
        ·
          refine ⟨18436873137160078736390533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24582497516213438315187377 18436873137160078736390533)
          ·
            refine ⟨3456913713217514763073225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18436873137160078736390533 3456913713217514763073225)
            ·
              refine ⟨2592685284913136072304919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456913713217514763073225 2592685284913136072304919)
              ·
                refine ⟨3889027927369704108457379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592685284913136072304919 3889027927369704108457379)
                ·
                  refine ⟨5833541891054556162686069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889027927369704108457379 5833541891054556162686069)
                  ·
                    refine ⟨546894552286364640251819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5833541891054556162686069 546894552286364640251819)
                    ·
                      rfl

theorem cell23_3195220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3195220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195220 prefixEnd_3195220 := by exact prefixLift 3195220
  have htrace : WordTrace (prefixWord ++ tailWord_3195220) baseStart_3195220 baseEnd_3195220 := by
    simpa [prefixWord, tailWord_3195220, baseEnd_3195220] using wordTrace_append hprefix tailTrace_3195220
  have hstable : (prefixWord ++ tailWord_3195220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195220).length < 2 ^ (prefixWord ++ tailWord_3195220).sum := by decide
  have hdescent : baseEnd_3195220 < baseStart_3195220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195223 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_3195223 : Nat := 118140960795 + 3195223 * 2 ^ 59
def prefixEnd_3195223 : Nat := 4983230072969 + 3 ^ 40 * 3195223 * 2
def baseEnd_3195223 : Nat := 1640685197301057409017943

theorem tailTrace_3195223 : CollatzResearch.WordTrace tailWord_3195223 prefixEnd_3195223 1640685197301057409017943 := by
  unfold tailWord_3195223
  simp only [CollatzResearch.WordTrace]
  refine ⟨116539356903260246488062323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77692904602173497658708215 116539356903260246488062323)
  ·
    refine ⟨174809035354890369732093485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116539356903260246488062323 174809035354890369732093485)
    ·
      refine ⟨65553388258083888649535057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174809035354890369732093485 65553388258083888649535057)
      ·
        refine ⟨49165041193562916487151293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65553388258083888649535057 49165041193562916487151293)
        ·
          refine ⟨18436890447586093682681735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49165041193562916487151293 18436890447586093682681735)
          ·
            refine ⟨27655335671379140524022603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18436890447586093682681735 27655335671379140524022603)
            ·
              refine ⟨41483003507068710786033905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27655335671379140524022603 41483003507068710786033905)
              ·
                refine ⟨31112252630301533089525429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41483003507068710786033905 31112252630301533089525429)
                ·
                  refine ⟨2916773684090768727143009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31112252630301533089525429 2916773684090768727143009)
                  ·
                    refine ⟨2187580263068076545357257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916773684090768727143009 2187580263068076545357257)
                    ·
                      refine ⟨1640685197301057409017943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187580263068076545357257 1640685197301057409017943)
                      ·
                        rfl

theorem cell23_3195223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_3195223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195223 prefixEnd_3195223 := by exact prefixLift 3195223
  have htrace : WordTrace (prefixWord ++ tailWord_3195223) baseStart_3195223 baseEnd_3195223 := by
    simpa [prefixWord, tailWord_3195223, baseEnd_3195223] using wordTrace_append hprefix tailTrace_3195223
  have hstable : (prefixWord ++ tailWord_3195223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195223).length < 2 ^ (prefixWord ++ tailWord_3195223).sum := by decide
  have hdescent : baseEnd_3195223 < baseStart_3195223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195240 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3195240 : Nat := 118140960795 + 3195240 * 2 ^ 59
def prefixEnd_3195240 : Nat := 4983230072969 + 3 ^ 40 * 3195240 * 2
def baseEnd_3195240 : Nat := 1640693926472183842505365

theorem tailTrace_3195240 : CollatzResearch.WordTrace tailWord_3195240 prefixEnd_3195240 1640693926472183842505365 := by
  unfold tailWord_3195240
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269988472099329195715587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77693317962799105594287449 58269988472099329195715587)
  ·
    refine ⟨87404982708148993793573381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58269988472099329195715587 87404982708148993793573381)
    ·
      refine ⟨16388434257777936336295009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87404982708148993793573381 16388434257777936336295009)
      ·
        refine ⟨12291325693333452252221257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16388434257777936336295009 12291325693333452252221257)
        ·
          refine ⟨9218494270000089189165943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12291325693333452252221257 9218494270000089189165943)
          ·
            refine ⟨13827741405000133783748915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218494270000089189165943 13827741405000133783748915)
            ·
              refine ⟨20741612107500200675623373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827741405000133783748915 20741612107500200675623373)
              ·
                refine ⟨7778104540312575253358765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20741612107500200675623373 7778104540312575253358765)
                ·
                  refine ⟨2916789202617215720009537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7778104540312575253358765 2916789202617215720009537)
                  ·
                    refine ⟨2187591901962911790007153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916789202617215720009537 2187591901962911790007153)
                    ·
                      refine ⟨1640693926472183842505365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187591901962911790007153 1640693926472183842505365)
                      ·
                        rfl

theorem cell23_3195240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3195240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195240 prefixEnd_3195240 := by exact prefixLift 3195240
  have htrace : WordTrace (prefixWord ++ tailWord_3195240) baseStart_3195240 baseEnd_3195240 := by
    simpa [prefixWord, tailWord_3195240, baseEnd_3195240] using wordTrace_append hprefix tailTrace_3195240
  have hstable : (prefixWord ++ tailWord_3195240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195240).length < 2 ^ (prefixWord ++ tailWord_3195240).sum := by decide
  have hdescent : baseEnd_3195240 < baseStart_3195240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195250 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3195250 : Nat := 118140960795 + 3195250 * 2 ^ 59
def prefixEnd_3195250 : Nat := 4983230072969 + 3 ^ 40 * 3195250 * 2
def baseEnd_3195250 : Nat := 546899687092909601126773

theorem tailTrace_3195250 : CollatzResearch.WordTrace tailWord_3195250 prefixEnd_3195250 546899687092909601126773 := by
  unfold tailWord_3195250
  simp only [CollatzResearch.WordTrace]
  refine ⟨29135085418540607524823801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77693561116108286732863469 29135085418540607524823801)
  ·
    refine ⟨21851314063905455643617851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29135085418540607524823801 21851314063905455643617851)
    ·
      refine ⟨32776971095858183465426777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21851314063905455643617851 32776971095858183465426777)
      ·
        refine ⟨24582728321893637599070083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32776971095858183465426777 24582728321893637599070083)
        ·
          refine ⟨36874092482840456398605125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24582728321893637599070083 36874092482840456398605125)
          ·
            refine ⟨6913892340532585574738461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36874092482840456398605125 6913892340532585574738461)
            ·
              refine ⟨2592709627699719590526923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6913892340532585574738461 2592709627699719590526923)
              ·
                refine ⟨3889064441549579385790385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592709627699719590526923 3889064441549579385790385)
                ·
                  refine ⟨2916798331162184539342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3889064441549579385790385 2916798331162184539342789)
                  ·
                    refine ⟨546899687092909601126773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2916798331162184539342789 546899687092909601126773)
                    ·
                      rfl

theorem cell23_3195250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3195250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195250 prefixEnd_3195250 := by exact prefixLift 3195250
  have htrace : WordTrace (prefixWord ++ tailWord_3195250) baseStart_3195250 baseEnd_3195250 := by
    simpa [prefixWord, tailWord_3195250, baseEnd_3195250] using wordTrace_append hprefix tailTrace_3195250
  have hstable : (prefixWord ++ tailWord_3195250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195250).length < 2 ^ (prefixWord ++ tailWord_3195250).sum := by decide
  have hdescent : baseEnd_3195250 < baseStart_3195250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195253 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3195253 : Nat := 118140960795 + 3195253 * 2 ^ 59
def prefixEnd_3195253 : Nat := 4983230072969 + 3 ^ 40 * 3195253 * 2
def baseEnd_3195253 : Nat := 1640700601720692291642805

theorem tailTrace_3195253 : CollatzResearch.WordTrace tailWord_3195253 prefixEnd_3195253 1640700601720692291642805 := by
  unfold tailWord_3195253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116540451093151561611654413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77693634062101041074436275 116540451093151561611654413)
  ·
    refine ⟨43702669159931835604370405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116540451093151561611654413 43702669159931835604370405)
    ·
      refine ⟨8194250467487219175819451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43702669159931835604370405 8194250467487219175819451)
      ·
        refine ⟨12291375701230828763729177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194250467487219175819451 12291375701230828763729177)
        ·
          refine ⟨9218531775923121572796883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12291375701230828763729177 9218531775923121572796883)
          ·
            refine ⟨13827797663884682359195325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218531775923121572796883 13827797663884682359195325)
            ·
              refine ⟨5185424123956755884698247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13827797663884682359195325 5185424123956755884698247)
              ·
                refine ⟨7778136185935133827047371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185424123956755884698247 7778136185935133827047371)
                ·
                  refine ⟨11667204278902700740571057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7778136185935133827047371 11667204278902700740571057)
                  ·
                    refine ⟨8750403209177025555428293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11667204278902700740571057 8750403209177025555428293)
                    ·
                      refine ⟨1640700601720692291642805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8750403209177025555428293 1640700601720692291642805)
                      ·
                        rfl

theorem cell23_3195253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3195253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195253 prefixEnd_3195253 := by exact prefixLift 3195253
  have htrace : WordTrace (prefixWord ++ tailWord_3195253) baseStart_3195253 baseEnd_3195253 := by
    simpa [prefixWord, tailWord_3195253, baseEnd_3195253] using wordTrace_append hprefix tailTrace_3195253
  have hstable : (prefixWord ++ tailWord_3195253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195253).length < 2 ^ (prefixWord ++ tailWord_3195253).sum := by decide
  have hdescent : baseEnd_3195253 < baseStart_3195253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195273 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_3195273 : Nat := 118140960795 + 3195273 * 2 ^ 59
def prefixEnd_3195273 : Nat := 4983230072969 + 3 ^ 40 * 3195273 * 2
def baseEnd_3195273 : Nat := 1640710871333782213392713

theorem tailTrace_3195273 : CollatzResearch.WordTrace tailWord_3195273 prefixEnd_3195273 1640710871333782213392713 := by
  unfold tailWord_3195273
  simp only [CollatzResearch.WordTrace]
  refine ⟨116541180553079105027382473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77694120368719403351588315 116541180553079105027382473)
  ·
    refine ⟨87405885414809328770536855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116541180553079105027382473 87405885414809328770536855)
    ·
      refine ⟨131108828122213993155805283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87405885414809328770536855 131108828122213993155805283)
      ·
        refine ⟨196663242183320989733707925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131108828122213993155805283 196663242183320989733707925)
        ·
          refine ⟨9218589477343171393767559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196663242183320989733707925 9218589477343171393767559)
          ·
            refine ⟨13827884216014757090651339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218589477343171393767559 13827884216014757090651339)
            ·
              refine ⟨20741826324022135635977009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827884216014757090651339 20741826324022135635977009)
              ·
                refine ⟨15556369743016601726982757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20741826324022135635977009 15556369743016601726982757)
                ·
                  refine ⟨2916819326815612823809267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15556369743016601726982757 2916819326815612823809267)
                  ·
                    refine ⟨4375228990223419235713901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2916819326815612823809267 4375228990223419235713901)
                    ·
                      refine ⟨1640710871333782213392713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4375228990223419235713901 1640710871333782213392713)
                      ·
                        rfl

theorem cell23_3195273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_3195273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195273 prefixEnd_3195273 := by exact prefixLift 3195273
  have htrace : WordTrace (prefixWord ++ tailWord_3195273) baseStart_3195273 baseEnd_3195273 := by
    simpa [prefixWord, tailWord_3195273, baseEnd_3195273] using wordTrace_append hprefix tailTrace_3195273
  have hstable : (prefixWord ++ tailWord_3195273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195273).length < 2 ^ (prefixWord ++ tailWord_3195273).sum := by decide
  have hdescent : baseEnd_3195273 < baseStart_3195273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195353 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 5]
def baseStart_3195353 : Nat := 118140960795 + 3195353 * 2 ^ 59
def prefixEnd_3195353 : Nat := 4983230072969 + 3 ^ 40 * 3195353 * 2
def baseEnd_3195353 : Nat := 182305772198460211154705

theorem tailTrace_3195353 : CollatzResearch.WordTrace tailWord_3195353 prefixEnd_3195353 182305772198460211154705 := by
  unfold tailWord_3195353
  simp only [CollatzResearch.WordTrace]
  refine ⟨116544098392789278690294713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77696065595192852460196475 116544098392789278690294713)
  ·
    refine ⟨87408073794591959017721035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116544098392789278690294713 87408073794591959017721035)
    ·
      refine ⟨131112110691887938526581553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87408073794591959017721035 131112110691887938526581553)
      ·
        refine ⟨98334083018915953894936165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131112110691887938526581553 98334083018915953894936165)
        ·
          refine ⟨18437640566046741355300531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98334083018915953894936165 18437640566046741355300531)
          ·
            refine ⟨27656460849070112032950797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437640566046741355300531 27656460849070112032950797)
            ·
              refine ⟨10371172818401292012356549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27656460849070112032950797 10371172818401292012356549)
              ·
                refine ⟨1944594903450242252316853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10371172818401292012356549 1944594903450242252316853)
                ·
                  refine ⟨182305772198460211154705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944594903450242252316853 182305772198460211154705)
                  ·
                    rfl

theorem cell23_3195353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 5].length) (baseStart_3195353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195353 prefixEnd_3195353 := by exact prefixLift 3195353
  have htrace : WordTrace (prefixWord ++ tailWord_3195353) baseStart_3195353 baseEnd_3195353 := by
    simpa [prefixWord, tailWord_3195353, baseEnd_3195353] using wordTrace_append hprefix tailTrace_3195353
  have hstable : (prefixWord ++ tailWord_3195353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195353).length < 2 ^ (prefixWord ++ tailWord_3195353).sum := by decide
  have hdescent : baseEnd_3195353 < baseStart_3195353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195398 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3195398 : Nat := 118140960795 + 3195398 * 2 ^ 59
def prefixEnd_3195398 : Nat := 4983230072969 + 3 ^ 40 * 3195398 * 2
def baseEnd_3195398 : Nat := 1640775056415594224329639

theorem tailTrace_3195398 : CollatzResearch.WordTrace tailWord_3195398 prefixEnd_3195398 1640775056415594224329639 := by
  unfold tailWord_3195398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642054364925820355490089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77697159785084167583788565 3642054364925820355490089)
  ·
    refine ⟨2731540773694365266617567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3642054364925820355490089 2731540773694365266617567)
    ·
      refine ⟨4097311160541547899926351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731540773694365266617567 4097311160541547899926351)
      ·
        refine ⟨6145966740812321849889527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097311160541547899926351 6145966740812321849889527)
        ·
          refine ⟨9218950111218482774834291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145966740812321849889527 9218950111218482774834291)
          ·
            refine ⟨13828425166827724162251437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218950111218482774834291 13828425166827724162251437)
            ·
              refine ⟨5185659437560396560844289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13828425166827724162251437 5185659437560396560844289)
              ·
                refine ⟨3889244578170297420633217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185659437560396560844289 3889244578170297420633217)
                ·
                  refine ⟨2916933433627723065474913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3889244578170297420633217 2916933433627723065474913)
                  ·
                    refine ⟨2187700075220792299106185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916933433627723065474913 2187700075220792299106185)
                    ·
                      refine ⟨1640775056415594224329639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187700075220792299106185 1640775056415594224329639)
                      ·
                        rfl

theorem cell23_3195398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3195398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195398 prefixEnd_3195398 := by exact prefixLift 3195398
  have htrace : WordTrace (prefixWord ++ tailWord_3195398) baseStart_3195398 baseEnd_3195398 := by
    simpa [prefixWord, tailWord_3195398, baseEnd_3195398] using wordTrace_append hprefix tailTrace_3195398
  have hstable : (prefixWord ++ tailWord_3195398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195398).length < 2 ^ (prefixWord ++ tailWord_3195398).sum := by decide
  have hdescent : baseEnd_3195398 < baseStart_3195398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195420 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3195420 : Nat := 118140960795 + 3195420 * 2 ^ 59
def prefixEnd_3195420 : Nat := 4983230072969 + 3 ^ 40 * 3195420 * 2
def baseEnd_3195420 : Nat := 1640786352989993138254537

theorem tailTrace_3195420 : CollatzResearch.WordTrace tailWord_3195420 prefixEnd_3195420 1640786352989993138254537 := by
  unfold tailWord_3195420
  simp only [CollatzResearch.WordTrace]
  refine ⟨58273271041773274566491857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77697694722364366088655809 58273271041773274566491857)
  ·
    refine ⟨43704953281329955924868893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58273271041773274566491857 43704953281329955924868893)
    ·
      refine ⟨16389357480498733471825835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43704953281329955924868893 16389357480498733471825835)
      ·
        refine ⟨24584036220748100207738753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389357480498733471825835 24584036220748100207738753)
        ·
          refine ⟨18438027165561075155804065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24584036220748100207738753 18438027165561075155804065)
          ·
            refine ⟨13828520374170806366853049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18438027165561075155804065 13828520374170806366853049)
            ·
              refine ⟨10371390280628104775139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828520374170806366853049 10371390280628104775139787)
              ·
                refine ⟨15557085420942157162709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371390280628104775139787 15557085420942157162709681)
                ·
                  refine ⟨11667814065706617872032261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557085420942157162709681 11667814065706617872032261)
                  ·
                    refine ⟨2187715137319990851006049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11667814065706617872032261 2187715137319990851006049)
                    ·
                      refine ⟨1640786352989993138254537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187715137319990851006049 1640786352989993138254537)
                      ·
                        rfl

theorem cell23_3195420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3195420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195420 prefixEnd_3195420 := by exact prefixLift 3195420
  have htrace : WordTrace (prefixWord ++ tailWord_3195420) baseStart_3195420 baseEnd_3195420 := by
    simpa [prefixWord, tailWord_3195420, baseEnd_3195420] using wordTrace_append hprefix tailTrace_3195420
  have hstable : (prefixWord ++ tailWord_3195420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195420).length < 2 ^ (prefixWord ++ tailWord_3195420).sum := by decide
  have hdescent : baseEnd_3195420 < baseStart_3195420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195503 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 6, 4]
def baseStart_3195503 : Nat := 118140960795 + 3195503 * 2 ^ 59
def prefixEnd_3195503 : Nat := 4983230072969 + 3 ^ 40 * 3195503 * 2
def baseEnd_3195503 : Nat := 546942990628105437838885

theorem tailTrace_3195503 : CollatzResearch.WordTrace tailWord_3195503 prefixEnd_3195503 546942990628105437838885 := by
  unfold tailWord_3195503
  simp only [CollatzResearch.WordTrace]
  refine ⟨116549569342245854308255163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77699712894830569538836775 116549569342245854308255163)
  ·
    refine ⟨174824354013368781462382745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116549569342245854308255163 174824354013368781462382745)
    ·
      refine ⟨131118265510026586096787059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174824354013368781462382745 131118265510026586096787059)
      ·
        refine ⟨196677398265039879145180589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131118265510026586096787059 196677398265039879145180589)
        ·
          refine ⟨73754024349389954679442721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196677398265039879145180589 73754024349389954679442721)
          ·
            refine ⟨55315518262042466009582041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73754024349389954679442721 55315518262042466009582041)
            ·
              refine ⟨41486638696531849507186531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55315518262042466009582041 41486638696531849507186531)
              ·
                refine ⟨62229958044797774260779797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41486638696531849507186531 62229958044797774260779797)
                ·
                  refine ⟨2917029283349895668474053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62229958044797774260779797 2917029283349895668474053)
                  ·
                    refine ⟨546942990628105437838885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2917029283349895668474053 546942990628105437838885)
                    ·
                      rfl

theorem cell23_3195503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_3195503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195503 prefixEnd_3195503 := by exact prefixLift 3195503
  have htrace : WordTrace (prefixWord ++ tailWord_3195503) baseStart_3195503 baseEnd_3195503 := by
    simpa [prefixWord, tailWord_3195503, baseEnd_3195503] using wordTrace_append hprefix tailTrace_3195503
  have hstable : (prefixWord ++ tailWord_3195503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195503).length < 2 ^ (prefixWord ++ tailWord_3195503).sum := by decide
  have hdescent : baseEnd_3195503 < baseStart_3195503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195520 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_3195520 : Nat := 118140960795 + 3195520 * 2 ^ 59
def prefixEnd_3195520 : Nat := 4983230072969 + 3 ^ 40 * 3195520 * 2
def baseEnd_3195520 : Nat := 546945900351814249001359

theorem tailTrace_3195520 : CollatzResearch.WordTrace tailWord_3195520 prefixEnd_3195520 546945900351814249001359 := by
  unfold tailWord_3195520
  simp only [CollatzResearch.WordTrace]
  refine ⟨58275094691592133105812007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77700126255456177474416009 58275094691592133105812007)
  ·
    refine ⟨87412642037388199658718011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58275094691592133105812007 87412642037388199658718011)
    ·
      refine ⟨131118963056082299488077017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87412642037388199658718011 131118963056082299488077017)
      ·
        refine ⟨98339222292061724616057763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131118963056082299488077017 98339222292061724616057763)
        ·
          refine ⟨147508833438092586924086645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98339222292061724616057763 147508833438092586924086645)
          ·
            refine ⟨13828953134821180024133123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147508833438092586924086645 13828953134821180024133123)
            ·
              refine ⟨20743429702231770036199685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13828953134821180024133123 20743429702231770036199685)
              ·
                refine ⟨3889393069168456881787441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20743429702231770036199685 3889393069168456881787441)
                ·
                  refine ⟨2917044801876342661340581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3889393069168456881787441 2917044801876342661340581)
                  ·
                    refine ⟨546945900351814249001359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2917044801876342661340581 546945900351814249001359)
                    ·
                      rfl

theorem cell23_3195520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_3195520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195520 prefixEnd_3195520 := by exact prefixLift 3195520
  have htrace : WordTrace (prefixWord ++ tailWord_3195520) baseStart_3195520 baseEnd_3195520 := by
    simpa [prefixWord, tailWord_3195520, baseEnd_3195520] using wordTrace_append hprefix tailTrace_3195520
  have hstable : (prefixWord ++ tailWord_3195520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195520).length < 2 ^ (prefixWord ++ tailWord_3195520).sum := by decide
  have hdescent : baseEnd_3195520 < baseStart_3195520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195527 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_3195527 : Nat := 118140960795 + 3195527 * 2 ^ 59
def prefixEnd_3195527 : Nat := 4983230072969 + 3 ^ 40 * 3195527 * 2
def baseEnd_3195527 : Nat := 1640841295420024219616545

theorem tailTrace_3195527 : CollatzResearch.WordTrace tailWord_3195527 prefixEnd_3195527 1640841295420024219616545 := by
  unfold tailWord_3195527
  simp only [CollatzResearch.WordTrace]
  refine ⟨116550444694158906407128835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77700296462772604271419223 116550444694158906407128835)
  ·
    refine ⟨174825667041238359610693253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116550444694158906407128835 174825667041238359610693253)
    ·
      refine ⟨32779812570232192427004985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174825667041238359610693253 32779812570232192427004985)
      ·
        refine ⟨24584859427674144320253739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32779812570232192427004985 24584859427674144320253739)
        ·
          refine ⟨36877289141511216480380609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24584859427674144320253739 36877289141511216480380609)
          ·
            refine ⟨27657966856133412360285457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36877289141511216480380609 27657966856133412360285457)
            ·
              refine ⟨20743475142100059270214093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27657966856133412360285457 20743475142100059270214093)
              ·
                refine ⟨7778803178287522226330285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20743475142100059270214093 7778803178287522226330285)
                ·
                  refine ⟨2917051191857820834873857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7778803178287522226330285 2917051191857820834873857)
                  ·
                    refine ⟨2187788393893365626155393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917051191857820834873857 2187788393893365626155393)
                    ·
                      refine ⟨1640841295420024219616545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187788393893365626155393 1640841295420024219616545)
                      ·
                        rfl

theorem cell23_3195527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_3195527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195527 prefixEnd_3195527 := by exact prefixLift 3195527
  have htrace : WordTrace (prefixWord ++ tailWord_3195527) baseStart_3195527 baseEnd_3195527 := by
    simpa [prefixWord, tailWord_3195527, baseEnd_3195527] using wordTrace_append hprefix tailTrace_3195527
  have hstable : (prefixWord ++ tailWord_3195527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195527).length < 2 ^ (prefixWord ++ tailWord_3195527).sum := by decide
  have hdescent : baseEnd_3195527 < baseStart_3195527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195620 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_3195620 : Nat := 118140960795 + 3195620 * 2 ^ 59
def prefixEnd_3195620 : Nat := 4983230072969 + 3 ^ 40 * 3195620 * 2
def baseEnd_3195620 : Nat := 1640889049120892355753617

theorem tailTrace_3195620 : CollatzResearch.WordTrace tailWord_3195620 prefixEnd_3195620 1640889049120892355753617 := by
  unfold tailWord_3195620
  simp only [CollatzResearch.WordTrace]
  refine ⟨58276918341410991645132157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77702557788547988860176209 58276918341410991645132157)
  ·
    refine ⟨21853844378029121866924559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58276918341410991645132157 21853844378029121866924559)
    ·
      refine ⟨32780766567043682800386839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853844378029121866924559 32780766567043682800386839)
      ·
        refine ⟨49171149850565524200580259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32780766567043682800386839 49171149850565524200580259)
        ·
          refine ⟨73756724775848286300870389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49171149850565524200580259 73756724775848286300870389)
          ·
            refine ⟨6914692947735776840706599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73756724775848286300870389 6914692947735776840706599)
            ·
              refine ⟨10372039421603665261059899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6914692947735776840706599 10372039421603665261059899)
              ·
                refine ⟨15558059132405497891589849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372039421603665261059899 15558059132405497891589849)
                ·
                  refine ⟨11668544349304123418692387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15558059132405497891589849 11668544349304123418692387)
                  ·
                    refine ⟨17502816523956185128038581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11668544349304123418692387 17502816523956185128038581)
                    ·
                      refine ⟨1640889049120892355753617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17502816523956185128038581 1640889049120892355753617)
                      ·
                        rfl

theorem cell23_3195620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_3195620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195620 prefixEnd_3195620 := by exact prefixLift 3195620
  have htrace : WordTrace (prefixWord ++ tailWord_3195620) baseStart_3195620 baseEnd_3195620 := by
    simpa [prefixWord, tailWord_3195620, baseEnd_3195620] using wordTrace_append hprefix tailTrace_3195620
  have hstable : (prefixWord ++ tailWord_3195620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195620).length < 2 ^ (prefixWord ++ tailWord_3195620).sum := by decide
  have hdescent : baseEnd_3195620 < baseStart_3195620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195633 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3195633 : Nat := 118140960795 + 3195633 * 2 ^ 59
def prefixEnd_3195633 : Nat := 4983230072969 + 3 ^ 40 * 3195633 * 2
def baseEnd_3195633 : Nat := 1640895724369400804891057

theorem tailTrace_3195633 : CollatzResearch.WordTrace tailWord_3195633 prefixEnd_3195633 1640895724369400804891057 := by
  unfold tailWord_3195633
  simp only [CollatzResearch.WordTrace]
  refine ⟨116554310831774886510487553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77702873887849924340325035 116554310831774886510487553)
  ·
    refine ⟨87415733123831164882865665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116554310831774886510487553 87415733123831164882865665)
    ·
      refine ⟨65561799842873373662149249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87415733123831164882865665 65561799842873373662149249)
      ·
        refine ⟨49171349882155030246611937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65561799842873373662149249 49171349882155030246611937)
        ·
          refine ⟨36878512411616272684958953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49171349882155030246611937 36878512411616272684958953)
          ·
            refine ⟨27658884308712204513719215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36878512411616272684958953 27658884308712204513719215)
            ·
              refine ⟨41488326463068306770578823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27658884308712204513719215 41488326463068306770578823)
              ·
                refine ⟨62232489694602460155868235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41488326463068306770578823 62232489694602460155868235)
                ·
                  refine ⟨93348734541903690233802353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62232489694602460155868235 93348734541903690233802353)
                  ·
                    refine ⟨70011550906427767675351765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93348734541903690233802353 70011550906427767675351765)
                    ·
                      refine ⟨1640895724369400804891057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70011550906427767675351765 1640895724369400804891057)
                      ·
                        rfl

theorem cell23_3195633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3195633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195633 prefixEnd_3195633 := by exact prefixLift 3195633
  have htrace : WordTrace (prefixWord ++ tailWord_3195633) baseStart_3195633 baseEnd_3195633 := by
    simpa [prefixWord, tailWord_3195633, baseEnd_3195633] using wordTrace_append hprefix tailTrace_3195633
  have hstable : (prefixWord ++ tailWord_3195633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195633).length < 2 ^ (prefixWord ++ tailWord_3195633).sum := by decide
  have hdescent : baseEnd_3195633 < baseStart_3195633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195634 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3195634 : Nat := 118140960795 + 3195634 * 2 ^ 59
def prefixEnd_3195634 : Nat := 4983230072969 + 3 ^ 40 * 3195634 * 2
def baseEnd_3195634 : Nat := 1640896237850055300978553

theorem tailTrace_3195634 : CollatzResearch.WordTrace tailWord_3195634 prefixEnd_3195634 1640896237850055300978553 := by
  unfold tailWord_3195634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29138586826192815920318489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77702898203180842454182637 29138586826192815920318489)
  ·
    refine ⟨21853940119644611940238867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29138586826192815920318489 21853940119644611940238867)
    ·
      refine ⟨32780910179466917910358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853940119644611940238867 32780910179466917910358301)
      ·
        refine ⟨12292841317300094216384363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32780910179466917910358301 12292841317300094216384363)
        ·
          refine ⟨18439261975950141324576545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12292841317300094216384363 18439261975950141324576545)
          ·
            refine ⟨13829446481962605993432409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18439261975950141324576545 13829446481962605993432409)
            ·
              refine ⟨10372084861471954495074307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13829446481962605993432409 10372084861471954495074307)
              ·
                refine ⟨15558127292207931742611461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372084861471954495074307 15558127292207931742611461)
                ·
                  refine ⟨2917148867288987201739649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15558127292207931742611461 2917148867288987201739649)
                  ·
                    refine ⟨2187861650466740401304737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917148867288987201739649 2187861650466740401304737)
                    ·
                      refine ⟨1640896237850055300978553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187861650466740401304737 1640896237850055300978553)
                      ·
                        rfl

theorem cell23_3195634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3195634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195634 prefixEnd_3195634 := by exact prefixLift 3195634
  have htrace : WordTrace (prefixWord ++ tailWord_3195634) baseStart_3195634 baseEnd_3195634 := by
    simpa [prefixWord, tailWord_3195634, baseEnd_3195634] using wordTrace_append hprefix tailTrace_3195634
  have hstable : (prefixWord ++ tailWord_3195634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195634).length < 2 ^ (prefixWord ++ tailWord_3195634).sum := by decide
  have hdescent : baseEnd_3195634 < baseStart_3195634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195653 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_3195653 : Nat := 118140960795 + 3195653 * 2 ^ 59
def prefixEnd_3195653 : Nat := 4983230072969 + 3 ^ 40 * 3195653 * 2
def baseEnd_3195653 : Nat := 546968664660830242213655

theorem tailTrace_3195653 : CollatzResearch.WordTrace tailWord_3195653 prefixEnd_3195653 546968664660830242213655 := by
  unfold tailWord_3195653
  simp only [CollatzResearch.WordTrace]
  refine ⟨116555040291702429926215613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77703360194468286617477075 116555040291702429926215613)
  ·
    refine ⟨43708140109388411222330855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116555040291702429926215613 43708140109388411222330855)
    ·
      refine ⟨65562210164082616833496283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43708140109388411222330855 65562210164082616833496283)
      ·
        refine ⟨98343315246123925250244425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65562210164082616833496283 98343315246123925250244425)
        ·
          refine ⟨73757486434592943937683319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98343315246123925250244425 73757486434592943937683319)
          ·
            refine ⟨110636229651889415906524979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73757486434592943937683319 110636229651889415906524979)
            ·
              refine ⟨165954344477834123859787469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110636229651889415906524979 165954344477834123859787469)
              ·
                refine ⟨62232879179187796447420301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165954344477834123859787469 62232879179187796447420301)
                ·
                  refine ⟨23337329692195423667782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62232879179187796447420301 23337329692195423667782613)
                  ·
                    refine ⟨546968664660830242213655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23337329692195423667782613 546968664660830242213655)
                    ·
                      rfl

theorem cell23_3195653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_3195653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195653 prefixEnd_3195653 := by exact prefixLift 3195653
  have htrace : WordTrace (prefixWord ++ tailWord_3195653) baseStart_3195653 baseEnd_3195653 := by
    simpa [prefixWord, tailWord_3195653, baseEnd_3195653] using wordTrace_append hprefix tailTrace_3195653
  have hstable : (prefixWord ++ tailWord_3195653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195653).length < 2 ^ (prefixWord ++ tailWord_3195653).sum := by decide
  have hdescent : baseEnd_3195653 < baseStart_3195653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195663 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_3195663 : Nat := 118140960795 + 3195663 * 2 ^ 59
def prefixEnd_3195663 : Nat := 4983230072969 + 3 ^ 40 * 3195663 * 2
def baseEnd_3195663 : Nat := 1640911128789035687515919

theorem tailTrace_3195663 : CollatzResearch.WordTrace tailWord_3195663 prefixEnd_3195663 1640911128789035687515919 := by
  unfold tailWord_3195663
  simp only [CollatzResearch.WordTrace]
  refine ⟨116555405021666201634079643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77703603347777467756053095 116555405021666201634079643)
  ·
    refine ⟨174833107532499302451119465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116555405021666201634079643 174833107532499302451119465)
    ·
      refine ⟨131124830649374476838339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174833107532499302451119465 131124830649374476838339599)
      ·
        refine ⟨196687245974061715257509399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131124830649374476838339599 196687245974061715257509399)
        ·
          refine ⟨295030868961092572886264099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196687245974061715257509399 295030868961092572886264099)
          ·
            refine ⟨442546303441638859329396149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295030868961092572886264099 442546303441638859329396149)
            ·
              refine ⟨41488715947653643062130889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442546303441638859329396149 41488715947653643062130889)
              ·
                refine ⟨31116536960740232296598167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41488715947653643062130889 31116536960740232296598167)
                ·
                  refine ⟨46674805441110348444897251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31116536960740232296598167 46674805441110348444897251)
                  ·
                    refine ⟨70012208161665522667345877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46674805441110348444897251 70012208161665522667345877)
                    ·
                      refine ⟨1640911128789035687515919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70012208161665522667345877 1640911128789035687515919)
                      ·
                        rfl

theorem cell23_3195663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_3195663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195663 prefixEnd_3195663 := by exact prefixLift 3195663
  have htrace : WordTrace (prefixWord ++ tailWord_3195663) baseStart_3195663 baseEnd_3195663 := by
    simpa [prefixWord, tailWord_3195663, baseEnd_3195663] using wordTrace_append hprefix tailTrace_3195663
  have hstable : (prefixWord ++ tailWord_3195663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195663).length < 2 ^ (prefixWord ++ tailWord_3195663).sum := by decide
  have hdescent : baseEnd_3195663 < baseStart_3195663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195680 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3195680 : Nat := 118140960795 + 3195680 * 2 ^ 59
def prefixEnd_3195680 : Nat := 4983230072969 + 3 ^ 40 * 3195680 * 2
def baseEnd_3195680 : Nat := 1640919857960162121003341

theorem tailTrace_3195680 : CollatzResearch.WordTrace tailWord_3195680 prefixEnd_3195680 1640919857960162121003341 := by
  unfold tailWord_3195680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58278012531302306768724247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77704016708403075691632329 58278012531302306768724247)
  ·
    refine ⟨87417018796953460153086371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58278012531302306768724247 87417018796953460153086371)
    ·
      refine ⟨131125528195430190229629557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87417018796953460153086371 131125528195430190229629557)
      ·
        refine ⟨12293018268321580334027771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131125528195430190229629557 12293018268321580334027771)
        ·
          refine ⟨18439527402482370501041657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12293018268321580334027771 18439527402482370501041657)
          ·
            refine ⟨13829645551861777875781243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18439527402482370501041657 13829645551861777875781243)
            ·
              refine ⟨20744468327792666813671865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829645551861777875781243 20744468327792666813671865)
              ·
                refine ⟨15558351245844500110253899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20744468327792666813671865 15558351245844500110253899)
                ·
                  refine ⟨23337526868766750165380849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15558351245844500110253899 23337526868766750165380849)
                  ·
                    refine ⟨17503145151575062624035637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23337526868766750165380849 17503145151575062624035637)
                    ·
                      refine ⟨1640919857960162121003341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17503145151575062624035637 1640919857960162121003341)
                      ·
                        rfl

theorem cell23_3195680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3195680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195680 prefixEnd_3195680 := by exact prefixLift 3195680
  have htrace : WordTrace (prefixWord ++ tailWord_3195680) baseStart_3195680 baseEnd_3195680 := by
    simpa [prefixWord, tailWord_3195680, baseEnd_3195680] using wordTrace_append hprefix tailTrace_3195680
  have hstable : (prefixWord ++ tailWord_3195680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195680).length < 2 ^ (prefixWord ++ tailWord_3195680).sum := by decide
  have hdescent : baseEnd_3195680 < baseStart_3195680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195694 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3195694 : Nat := 118140960795 + 3195694 * 2 ^ 59
def prefixEnd_3195694 : Nat := 4983230072969 + 3 ^ 40 * 3195694 * 2
def baseEnd_3195694 : Nat := 1640927046689325066228277

theorem tailTrace_3195694 : CollatzResearch.WordTrace tailWord_3195694 prefixEnd_3195694 1640927046689325066228277 := by
  unfold tailWord_3195694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569566960569236741057267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77704357123035929285638757 14569566960569236741057267)
  ·
    refine ⟨21854350440853855111585901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14569566960569236741057267 21854350440853855111585901)
    ·
      refine ⟨8195381415320195666844713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21854350440853855111585901 8195381415320195666844713)
      ·
        refine ⟨6146536061490146750133535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8195381415320195666844713 6146536061490146750133535)
        ·
          refine ⟨9219804092235220125200303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146536061490146750133535 9219804092235220125200303)
          ·
            refine ⟨13829706138352830187800455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219804092235220125200303 13829706138352830187800455)
            ·
              refine ⟨20744559207529245281700683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829706138352830187800455 20744559207529245281700683)
              ·
                refine ⟨31116838811293867922551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20744559207529245281700683 31116838811293867922551025)
                ·
                  refine ⟨23337629108470400941913269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31116838811293867922551025 23337629108470400941913269)
                  ·
                    refine ⟨2187902728919100088304369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23337629108470400941913269 2187902728919100088304369)
                    ·
                      refine ⟨1640927046689325066228277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187902728919100088304369 1640927046689325066228277)
                      ·
                        rfl

theorem cell23_3195694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3195694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195694 prefixEnd_3195694 := by exact prefixLift 3195694
  have htrace : WordTrace (prefixWord ++ tailWord_3195694) baseStart_3195694 baseEnd_3195694 := by
    simpa [prefixWord, tailWord_3195694, baseEnd_3195694] using wordTrace_append hprefix tailTrace_3195694
  have hstable : (prefixWord ++ tailWord_3195694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195694).length < 2 ^ (prefixWord ++ tailWord_3195694).sum := by decide
  have hdescent : baseEnd_3195694 < baseStart_3195694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195724 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3195724 : Nat := 118140960795 + 3195724 * 2 ^ 59
def prefixEnd_3195724 : Nat := 4983230072969 + 3 ^ 40 * 3195724 * 2
def baseEnd_3195724 : Nat := 1640942451108959948853139

theorem tailTrace_3195724 : CollatzResearch.WordTrace tailWord_3195724 prefixEnd_3195724 1640942451108959948853139 := by
  unfold tailWord_3195724
  simp only [CollatzResearch.WordTrace]
  refine ⟨58278814937222604526025113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77705086582963472701366817 58278814937222604526025113)
  ·
    refine ⟨43709111202916953394518835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58278814937222604526025113 43709111202916953394518835)
    ·
      refine ⟨65563666804375430091778253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43709111202916953394518835 65563666804375430091778253)
      ·
        refine ⟨24586375051640786284416845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65563666804375430091778253 24586375051640786284416845)
        ·
          refine ⟨9219890644365294856656317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24586375051640786284416845 9219890644365294856656317)
          ·
            refine ⟨3457458991636985571246119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9219890644365294856656317 3457458991636985571246119)
            ·
              refine ⟨5186188487455478356869179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457458991636985571246119 5186188487455478356869179)
              ·
                refine ⟨7779282731183217535303769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186188487455478356869179 7779282731183217535303769)
                ·
                  refine ⟨5834462048387413151477827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779282731183217535303769 5834462048387413151477827)
                  ·
                    refine ⟨8751693072581119727216741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5834462048387413151477827 8751693072581119727216741)
                    ·
                      refine ⟨1640942451108959948853139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8751693072581119727216741 1640942451108959948853139)
                      ·
                        rfl

theorem cell23_3195724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3195724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195724 prefixEnd_3195724 := by exact prefixLift 3195724
  have htrace : WordTrace (prefixWord ++ tailWord_3195724) baseStart_3195724 baseEnd_3195724 := by
    simpa [prefixWord, tailWord_3195724, baseEnd_3195724] using wordTrace_append hprefix tailTrace_3195724
  have hstable : (prefixWord ++ tailWord_3195724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195724).length < 2 ^ (prefixWord ++ tailWord_3195724).sum := by decide
  have hdescent : baseEnd_3195724 < baseStart_3195724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195730 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3195730 : Nat := 118140960795 + 3195730 * 2 ^ 59
def prefixEnd_3195730 : Nat := 4983230072969 + 3 ^ 40 * 3195730 * 2
def baseEnd_3195730 : Nat := 182327281332542991708679

theorem tailTrace_3195730 : CollatzResearch.WordTrace tailWord_3195730 prefixEnd_3195730 182327281332542991708679 := by
  unfold tailWord_3195730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29139462178105868019192161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77705232474948981384512429 29139462178105868019192161)
  ·
    refine ⟨21854596633579401014394121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29139462178105868019192161 21854596633579401014394121)
    ·
      refine ⟨16390947475184550760795591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21854596633579401014394121 16390947475184550760795591)
      ·
        refine ⟨24586421212776826141193387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390947475184550760795591 24586421212776826141193387)
        ·
          refine ⟨36879631819165239211790081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24586421212776826141193387 36879631819165239211790081)
          ·
            refine ⟨27659723864373929408842561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36879631819165239211790081 27659723864373929408842561)
            ·
              refine ⟨20744792898280447056631921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27659723864373929408842561 20744792898280447056631921)
              ·
                refine ⟨15558594673710335292473941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20744792898280447056631921 15558594673710335292473941)
                ·
                  refine ⟨182327281332542991708679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15558594673710335292473941 182327281332542991708679)
                  ·
                    rfl

theorem cell23_3195730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3195730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195730 prefixEnd_3195730 := by exact prefixLift 3195730
  have htrace : WordTrace (prefixWord ++ tailWord_3195730) baseStart_3195730 baseEnd_3195730 := by
    simpa [prefixWord, tailWord_3195730, baseEnd_3195730] using wordTrace_append hprefix tailTrace_3195730
  have hstable : (prefixWord ++ tailWord_3195730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195730).length < 2 ^ (prefixWord ++ tailWord_3195730).sum := by decide
  have hdescent : baseEnd_3195730 < baseStart_3195730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195747 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 6]
def baseStart_3195747 : Nat := 118140960795 + 3195747 * 2 ^ 59
def prefixEnd_3195747 : Nat := 4983230072969 + 3 ^ 40 * 3195747 * 2
def baseEnd_3195747 : Nat := 182328251240445928762837

theorem tailTrace_3195747 : CollatzResearch.WordTrace tailWord_3195747 prefixEnd_3195747 182328251240445928762837 := by
  unfold tailWord_3195747
  simp only [CollatzResearch.WordTrace]
  refine ⟨116558468753361883980137495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77705645835574589320091663 116558468753361883980137495)
  ·
    refine ⟨174837703130042825970206243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116558468753361883980137495 174837703130042825970206243)
    ·
      refine ⟨262256554695064238955309365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174837703130042825970206243 262256554695064238955309365)
      ·
        refine ⟨24586552002662272402060253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262256554695064238955309365 24586552002662272402060253)
        ·
          refine ⟨9219957000998352150772595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24586552002662272402060253 9219957000998352150772595)
          ·
            refine ⟨13829935501497528226158893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219957000998352150772595 13829935501497528226158893)
            ·
              refine ⟨5186225813061573084809585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13829935501497528226158893 5186225813061573084809585)
              ·
                refine ⟨3889669359796179813607189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186225813061573084809585 3889669359796179813607189)
                ·
                  refine ⟨182328251240445928762837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3889669359796179813607189 182328251240445928762837)
                  ·
                    rfl

theorem cell23_3195747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 6].length) (baseStart_3195747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195747 prefixEnd_3195747 := by exact prefixLift 3195747
  have htrace : WordTrace (prefixWord ++ tailWord_3195747) baseStart_3195747 baseEnd_3195747 := by
    simpa [prefixWord, tailWord_3195747, baseEnd_3195747] using wordTrace_append hprefix tailTrace_3195747
  have hstable : (prefixWord ++ tailWord_3195747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195747).length < 2 ^ (prefixWord ++ tailWord_3195747).sum := by decide
  have hdescent : baseEnd_3195747 < baseStart_3195747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195760 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_3195760 : Nat := 118140960795 + 3195760 * 2 ^ 59
def prefixEnd_3195760 : Nat := 4983230072969 + 3 ^ 40 * 3195760 * 2
def baseEnd_3195760 : Nat := 546986978804173936000991

theorem tailTrace_3195760 : CollatzResearch.WordTrace tailWord_3195760 prefixEnd_3195760 546986978804173936000991 := by
  unfold tailWord_3195760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279471451157393600180367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77705961934876524800240489 58279471451157393600180367)
  ·
    refine ⟨87419207176736090400270551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58279471451157393600180367 87419207176736090400270551)
    ·
      refine ⟨131128810765104135600405827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87419207176736090400270551 131128810765104135600405827)
      ·
        refine ⟨196693216147656203400608741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131128810765104135600405827 196693216147656203400608741)
        ·
          refine ⟨36879978027685538137614139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196693216147656203400608741 36879978027685538137614139)
          ·
            refine ⟨55319967041528307206421209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36879978027685538137614139 55319967041528307206421209)
            ·
              refine ⟨41489975281146230404815907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55319967041528307206421209 41489975281146230404815907)
              ·
                refine ⟨62234962921719345607223861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41489975281146230404815907 62234962921719345607223861)
                ·
                  refine ⟨5834527773911188650677237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62234962921719345607223861 5834527773911188650677237)
                  ·
                    refine ⟨546986978804173936000991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5834527773911188650677237 546986978804173936000991)
                    ·
                      rfl

theorem cell23_3195760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_3195760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195760 prefixEnd_3195760 := by exact prefixLift 3195760
  have htrace : WordTrace (prefixWord ++ tailWord_3195760) baseStart_3195760 baseEnd_3195760 := by
    simpa [prefixWord, tailWord_3195760, baseEnd_3195760] using wordTrace_append hprefix tailTrace_3195760
  have hstable : (prefixWord ++ tailWord_3195760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195760).length < 2 ^ (prefixWord ++ tailWord_3195760).sum := by decide
  have hdescent : baseEnd_3195760 < baseStart_3195760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195784 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_3195784 : Nat := 118140960795 + 3195784 * 2 ^ 59
def prefixEnd_3195784 : Nat := 4983230072969 + 3 ^ 40 * 3195784 * 2
def baseEnd_3195784 : Nat := 1640973259948229714102863

theorem tailTrace_3195784 : CollatzResearch.WordTrace tailWord_3195784 prefixEnd_3195784 1640973259948229714102863 := by
  unfold tailWord_3195784
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279909127113919649617203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77706545502818559532822937 58279909127113919649617203)
  ·
    refine ⟨87419863690670879474425805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58279909127113919649617203 87419863690670879474425805)
    ·
      refine ⟨32782448884001579802909677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87419863690670879474425805 32782448884001579802909677)
      ·
        refine ⟨12293418331500592426091129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32782448884001579802909677 12293418331500592426091129)
        ·
          refine ⟨9220063748625444319568347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12293418331500592426091129 9220063748625444319568347)
          ·
            refine ⟨13830095622938166479352521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220063748625444319568347 13830095622938166479352521)
            ·
              refine ⟨10372571717203624859514391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830095622938166479352521 10372571717203624859514391)
              ·
                refine ⟨15558857575805437289271587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372571717203624859514391 15558857575805437289271587)
                ·
                  refine ⟨23338286363708155933907381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15558857575805437289271587 23338286363708155933907381)
                  ·
                    refine ⟨2187964346597639618803817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23338286363708155933907381 2187964346597639618803817)
                    ·
                      refine ⟨1640973259948229714102863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2187964346597639618803817 1640973259948229714102863)
                      ·
                        rfl

theorem cell23_3195784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_3195784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195784 prefixEnd_3195784 := by exact prefixLift 3195784
  have htrace : WordTrace (prefixWord ++ tailWord_3195784) baseStart_3195784 baseEnd_3195784 := by
    simpa [prefixWord, tailWord_3195784, baseEnd_3195784] using wordTrace_append hprefix tailTrace_3195784
  have hstable : (prefixWord ++ tailWord_3195784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195784).length < 2 ^ (prefixWord ++ tailWord_3195784).sum := by decide
  have hdescent : baseEnd_3195784 < baseStart_3195784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195817 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_3195817 : Nat := 118140960795 + 3195817 * 2 ^ 59
def prefixEnd_3195817 : Nat := 4983230072969 + 3 ^ 40 * 3195817 * 2
def baseEnd_3195817 : Nat := 1640990204809828084990211

theorem tailTrace_3195817 : CollatzResearch.WordTrace tailWord_3195817 prefixEnd_3195817 1640990204809828084990211 := by
  unfold tailWord_3195817
  simp only [CollatzResearch.WordTrace]
  refine ⟨116561021863108285935185705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77707347908738857290123803 116561021863108285935185705)
  ·
    refine ⟨87420766397331214451389279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116561021863108285935185705 87420766397331214451389279)
    ·
      refine ⟨131131149595996821677083919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87420766397331214451389279 131131149595996821677083919)
      ·
        refine ⟨196696724393995232515625879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131131149595996821677083919 196696724393995232515625879)
        ·
          refine ⟨295045086590992848773438819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196696724393995232515625879 295045086590992848773438819)
          ·
            refine ⟨442567629886489273160158229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295045086590992848773438819 442567629886489273160158229)
            ·
              refine ⟨20745357650929184679382417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 442567629886489273160158229 20745357650929184679382417)
              ·
                refine ⟨15559018238196888509536813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20745357650929184679382417 15559018238196888509536813)
                ·
                  refine ⟨5834631839323833191076305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15559018238196888509536813 5834631839323833191076305)
                  ·
                    refine ⟨4375973879492874893307229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834631839323833191076305 4375973879492874893307229)
                    ·
                      refine ⟨1640990204809828084990211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4375973879492874893307229 1640990204809828084990211)
                      ·
                        rfl

theorem cell23_3195817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_3195817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195817 prefixEnd_3195817 := by exact prefixLift 3195817
  have htrace : WordTrace (prefixWord ++ tailWord_3195817) baseStart_3195817 baseEnd_3195817 := by
    simpa [prefixWord, tailWord_3195817, baseEnd_3195817] using wordTrace_append hprefix tailTrace_3195817
  have hstable : (prefixWord ++ tailWord_3195817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195817).length < 2 ^ (prefixWord ++ tailWord_3195817).sum := by decide
  have hdescent : baseEnd_3195817 < baseStart_3195817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195828 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3195828 : Nat := 118140960795 + 3195828 * 2 ^ 59
def prefixEnd_3195828 : Nat := 4983230072969 + 3 ^ 40 * 3195828 * 2
def baseEnd_3195828 : Nat := 546998617699009180650887

theorem tailTrace_3195828 : CollatzResearch.WordTrace tailWord_3195828 prefixEnd_3195828 546998617699009180650887 := by
  unfold tailWord_3195828
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280711533034217406918069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77707615377378956542557425 58280711533034217406918069)
  ·
    refine ⟨5463816706221957881898569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58280711533034217406918069 5463816706221957881898569)
    ·
      refine ⟨4097862529666468411423927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5463816706221957881898569 4097862529666468411423927)
      ·
        refine ⟨6146793794499702617135891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097862529666468411423927 6146793794499702617135891)
        ·
          refine ⟨9220190691749553925703837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146793794499702617135891 9220190691749553925703837)
          ·
            refine ⟨3457571509406082722138939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9220190691749553925703837 3457571509406082722138939)
            ·
              refine ⟨5186357264109124083208409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457571509406082722138939 5186357264109124083208409)
              ·
                refine ⟨3889767948081843062406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186357264109124083208409 3889767948081843062406307)
                ·
                  refine ⟨5834651922122764593609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889767948081843062406307 5834651922122764593609461)
                  ·
                    refine ⟨546998617699009180650887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5834651922122764593609461 546998617699009180650887)
                    ·
                      rfl

theorem cell23_3195828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3195828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195828 prefixEnd_3195828 := by exact prefixLift 3195828
  have htrace : WordTrace (prefixWord ++ tailWord_3195828) baseStart_3195828 baseEnd_3195828 := by
    simpa [prefixWord, tailWord_3195828, baseEnd_3195828] using wordTrace_append hprefix tailTrace_3195828
  have hstable : (prefixWord ++ tailWord_3195828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195828).length < 2 ^ (prefixWord ++ tailWord_3195828).sum := by decide
  have hdescent : baseEnd_3195828 < baseStart_3195828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195847 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3195847 : Nat := 118140960795 + 3195847 * 2 ^ 59
def prefixEnd_3195847 : Nat := 4983230072969 + 3 ^ 40 * 3195847 * 2
def baseEnd_3195847 : Nat := 1641005609229462967615073

theorem tailTrace_3195847 : CollatzResearch.WordTrace tailWord_3195847 prefixEnd_3195847 1641005609229462967615073 := by
  unfold tailWord_3195847
  simp only [CollatzResearch.WordTrace]
  refine ⟨116562116052999601058777795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77708077368666400705851863 116562116052999601058777795)
  ·
    refine ⟨174843174079499401588166693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116562116052999601058777795 174843174079499401588166693)
    ·
      refine ⟨32783095139906137797781255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174843174079499401588166693 32783095139906137797781255)
      ·
        refine ⟨49174642709859206696671883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32783095139906137797781255 49174642709859206696671883)
        ·
          refine ⟨73761964064788810045007825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49174642709859206696671883 73761964064788810045007825)
          ·
            refine ⟨55321473048591607533755869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73761964064788810045007825 55321473048591607533755869)
            ·
              refine ⟨20745552393221852825158451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55321473048591607533755869 20745552393221852825158451)
              ·
                refine ⟨31118328589832779237737677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745552393221852825158451 31118328589832779237737677)
                ·
                  refine ⟨11669373221187292214151629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31118328589832779237737677 11669373221187292214151629)
                  ·
                    refine ⟨4376014957945234580306861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11669373221187292214151629 4376014957945234580306861)
                    ·
                      refine ⟨1641005609229462967615073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376014957945234580306861 1641005609229462967615073)
                      ·
                        rfl

theorem cell23_3195847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3195847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195847 prefixEnd_3195847 := by exact prefixLift 3195847
  have htrace : WordTrace (prefixWord ++ tailWord_3195847) baseStart_3195847 baseEnd_3195847 := by
    simpa [prefixWord, tailWord_3195847, baseEnd_3195847] using wordTrace_append hprefix tailTrace_3195847
  have hstable : (prefixWord ++ tailWord_3195847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195847).length < 2 ^ (prefixWord ++ tailWord_3195847).sum := by decide
  have hdescent : baseEnd_3195847 < baseStart_3195847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195851 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 1, 2, 3]
def baseStart_3195851 : Nat := 118140960795 + 3195851 * 2 ^ 59
def prefixEnd_3195851 : Nat := 4983230072969 + 3 ^ 40 * 3195851 * 2
def baseEnd_3195851 : Nat := 1641007663152080951965055

theorem tailTrace_3195851 : CollatzResearch.WordTrace tailWord_3195851 prefixEnd_3195851 1641007663152080951965055 := by
  unfold tailWord_3195851
  simp only [CollatzResearch.WordTrace]
  refine ⟨116562261944985109741923407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77708174629990073161282271 116562261944985109741923407)
  ·
    refine ⟨174843392917477664612885111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116562261944985109741923407 174843392917477664612885111)
    ·
      refine ⟨262265089376216496919327667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174843392917477664612885111 262265089376216496919327667)
      ·
        refine ⟨393397634064324745378991501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262265089376216496919327667 393397634064324745378991501)
        ·
          refine ⟨147524112774121779517121813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393397634064324745378991501 147524112774121779517121813)
          ·
            refine ⟨6915192786286958414865085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147524112774121779517121813 6915192786286958414865085)
            ·
              refine ⟨2593197294857609405574407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6915192786286958414865085 2593197294857609405574407)
              ·
                refine ⟨3889795942286414108361611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593197294857609405574407 3889795942286414108361611)
                ·
                  refine ⟨5834693913429621162542417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889795942286414108361611 5834693913429621162542417)
                  ·
                    refine ⟨4376020435072215871906813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834693913429621162542417 4376020435072215871906813)
                    ·
                      refine ⟨1641007663152080951965055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376020435072215871906813 1641007663152080951965055)
                      ·
                        rfl

theorem cell23_3195851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 2, 3].length) (baseStart_3195851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195851 prefixEnd_3195851 := by exact prefixLift 3195851
  have htrace : WordTrace (prefixWord ++ tailWord_3195851) baseStart_3195851 baseEnd_3195851 := by
    simpa [prefixWord, tailWord_3195851, baseEnd_3195851] using wordTrace_append hprefix tailTrace_3195851
  have hstable : (prefixWord ++ tailWord_3195851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195851).length < 2 ^ (prefixWord ++ tailWord_3195851).sum := by decide
  have hdescent : baseEnd_3195851 < baseStart_3195851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195865 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 1, 2, 2]
def baseStart_3195865 : Nat := 118140960795 + 3195865 * 2 ^ 59
def prefixEnd_3195865 : Nat := 4983230072969 + 3 ^ 40 * 3195865 * 2
def baseEnd_3195865 : Nat := 1641014851881243897189991

theorem tailTrace_3195865 : CollatzResearch.WordTrace tailWord_3195865 prefixEnd_3195865 1641014851881243897189991 := by
  unfold tailWord_3195865
  simp only [CollatzResearch.WordTrace]
  refine ⟨116562772566934390132933049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77708515044622926755288699 116562772566934390132933049)
  ·
    refine ⟨87422079425200792599699787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116562772566934390132933049 87422079425200792599699787)
    ·
      refine ⟨131133119137801188899549681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87422079425200792599699787 131133119137801188899549681)
      ·
        refine ⟨98349839353350891674662261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131133119137801188899549681 98349839353350891674662261)
        ·
          refine ⟨9220297439376646094499587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98349839353350891674662261 9220297439376646094499587)
          ·
            refine ⟨13830446159064969141749381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220297439376646094499587 13830446159064969141749381)
            ·
              refine ⟨2593208654824681714078009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13830446159064969141749381 2593208654824681714078009)
              ·
                refine ⟨1944906491118511285558507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593208654824681714078009 1944906491118511285558507)
                ·
                  refine ⟨2917359736677766928337761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944906491118511285558507 2917359736677766928337761)
                  ·
                    refine ⟨2188019802508325196253321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917359736677766928337761 2188019802508325196253321)
                    ·
                      refine ⟨1641014851881243897189991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188019802508325196253321 1641014851881243897189991)
                      ·
                        rfl

theorem cell23_3195865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_3195865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195865 prefixEnd_3195865 := by exact prefixLift 3195865
  have htrace : WordTrace (prefixWord ++ tailWord_3195865) baseStart_3195865 baseEnd_3195865 := by
    simpa [prefixWord, tailWord_3195865, baseEnd_3195865] using wordTrace_append hprefix tailTrace_3195865
  have hstable : (prefixWord ++ tailWord_3195865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195865).length < 2 ^ (prefixWord ++ tailWord_3195865).sum := by decide
  have hdescent : baseEnd_3195865 < baseStart_3195865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195902 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3195902 : Nat := 118140960795 + 3195902 * 2 ^ 59
def prefixEnd_3195902 : Nat := 4983230072969 + 3 ^ 40 * 3195902 * 2
def baseEnd_3195902 : Nat := 1641033850665460252427321

theorem tailTrace_3195902 : CollatzResearch.WordTrace tailWord_3195902 prefixEnd_3195902 1641033850665460252427321 := by
  unfold tailWord_3195902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570515258475043181503745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77709414711866896968019973 14570515258475043181503745)
  ·
    refine ⟨10927886443856282386127809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14570515258475043181503745 10927886443856282386127809)
    ·
      refine ⟨8195914832892211789595857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10927886443856282386127809 8195914832892211789595857)
      ·
        refine ⟨6146936124669158842196893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8195914832892211789595857 6146936124669158842196893)
        ·
          refine ⟨2305101046750934565823835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6146936124669158842196893 2305101046750934565823835)
          ·
            refine ⟨3457651570126401848735753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305101046750934565823835 3457651570126401848735753)
            ·
              refine ⟨2593238677594801386551815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457651570126401848735753 2593238677594801386551815)
              ·
                refine ⟨3889858016392202079827723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593238677594801386551815 3889858016392202079827723)
                ·
                  refine ⟨5834787024588303119741585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889858016392202079827723 5834787024588303119741585)
                  ·
                    refine ⟨4376090268441227339806189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834787024588303119741585 4376090268441227339806189)
                    ·
                      refine ⟨1641033850665460252427321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376090268441227339806189 1641033850665460252427321)
                      ·
                        rfl

theorem cell23_3195902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3195902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195902 prefixEnd_3195902 := by exact prefixLift 3195902
  have htrace : WordTrace (prefixWord ++ tailWord_3195902) baseStart_3195902 baseEnd_3195902 := by
    simpa [prefixWord, tailWord_3195902, baseEnd_3195902] using wordTrace_append hprefix tailTrace_3195902
  have hstable : (prefixWord ++ tailWord_3195902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195902).length < 2 ^ (prefixWord ++ tailWord_3195902).sum := by decide
  have hdescent : baseEnd_3195902 < baseStart_3195902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195938 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_3195938 : Nat := 118140960795 + 3195938 * 2 ^ 59
def prefixEnd_3195938 : Nat := 4983230072969 + 3 ^ 40 * 3195938 * 2
def baseEnd_3195938 : Nat := 1641052335969022111577155

theorem tailTrace_3195938 : CollatzResearch.WordTrace tailWord_3195938 prefixEnd_3195938 1641052335969022111577155 := by
  unfold tailWord_3195938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29141358773917480900085117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77710290063779949066893645 29141358773917480900085117)
  ·
    refine ⟨10928009540219055337531919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29141358773917480900085117 10928009540219055337531919)
    ·
      refine ⟨16392014310328583006297879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10928009540219055337531919 16392014310328583006297879)
      ·
        refine ⟨24588021465492874509446819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16392014310328583006297879 24588021465492874509446819)
        ·
          refine ⟨36882032198239311764170229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24588021465492874509446819 36882032198239311764170229)
          ·
            refine ⟨3457690518584935477890959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36882032198239311764170229 3457690518584935477890959)
            ·
              refine ⟨5186535777877403216836439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457690518584935477890959 5186535777877403216836439)
              ·
                refine ⟨7779803666816104825254659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186535777877403216836439 7779803666816104825254659)
                ·
                  refine ⟨11669705500224157237881989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779803666816104825254659 11669705500224157237881989)
                  ·
                    refine ⟨2188069781292029482102873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11669705500224157237881989 2188069781292029482102873)
                    ·
                      refine ⟨1641052335969022111577155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188069781292029482102873 1641052335969022111577155)
                      ·
                        rfl

theorem cell23_3195938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_3195938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195938 prefixEnd_3195938 := by exact prefixLift 3195938
  have htrace : WordTrace (prefixWord ++ tailWord_3195938) baseStart_3195938 baseEnd_3195938 := by
    simpa [prefixWord, tailWord_3195938, baseEnd_3195938] using wordTrace_append hprefix tailTrace_3195938
  have hstable : (prefixWord ++ tailWord_3195938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195938).length < 2 ^ (prefixWord ++ tailWord_3195938).sum := by decide
  have hdescent : baseEnd_3195938 < baseStart_3195938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195961 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 5]
def baseStart_3195961 : Nat := 118140960795 + 3195961 * 2 ^ 59
def prefixEnd_3195961 : Nat := 4983230072969 + 3 ^ 40 * 3195961 * 2
def baseEnd_3195961 : Nat := 182340460669341724621061

theorem tailTrace_3195961 : CollatzResearch.WordTrace tailWord_3195961 prefixEnd_3195961 182340460669341724621061 := by
  unfold tailWord_3195961
  simp only [CollatzResearch.WordTrace]
  refine ⟨116566273974586598528427737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77710849316391065685618491 116566273974586598528427737)
  ·
    refine ⟨87424705480939948896320803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116566273974586598528427737 87424705480939948896320803)
    ·
      refine ⟨131137058221409923344481205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87424705480939948896320803 131137058221409923344481205)
      ·
        refine ⟨12294099208257180313545113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131137058221409923344481205 12294099208257180313545113)
        ·
          refine ⟨9220574406192885235158835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12294099208257180313545113 9220574406192885235158835)
          ·
            refine ⟨13830861609289327852738253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220574406192885235158835 13830861609289327852738253)
            ·
              refine ⟨5186573103483497944776845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13830861609289327852738253 5186573103483497944776845)
              ·
                refine ⟨1944964913806311729291317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186573103483497944776845 1944964913806311729291317)
                ·
                  refine ⟨182340460669341724621061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944964913806311729291317 182340460669341724621061)
                  ·
                    rfl

theorem cell23_3195961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 5].length) (baseStart_3195961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195961 prefixEnd_3195961 := by exact prefixLift 3195961
  have htrace : WordTrace (prefixWord ++ tailWord_3195961) baseStart_3195961 baseEnd_3195961 := by
    simpa [prefixWord, tailWord_3195961, baseEnd_3195961] using wordTrace_append hprefix tailTrace_3195961
  have hstable : (prefixWord ++ tailWord_3195961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195961).length < 2 ^ (prefixWord ++ tailWord_3195961).sum := by decide
  have hdescent : baseEnd_3195961 < baseStart_3195961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195967 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_3195967 : Nat := 118140960795 + 3195967 * 2 ^ 59
def prefixEnd_3195967 : Nat := 4983230072969 + 3 ^ 40 * 3195967 * 2
def baseEnd_3195967 : Nat := 1641067226908002498114521

theorem tailTrace_3195967 : CollatzResearch.WordTrace tailWord_3195967 prefixEnd_3195967 1641067226908002498114521 := by
  unfold tailWord_3195967
  simp only [CollatzResearch.WordTrace]
  refine ⟨116566492812564861553146155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77710995208376574368764103 116566492812564861553146155)
  ·
    refine ⟨174849739218847292329719233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116566492812564861553146155 174849739218847292329719233)
    ·
      refine ⟨131137304414135469247289425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174849739218847292329719233 131137304414135469247289425)
      ·
        refine ⟨98352978310601601935467069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131137304414135469247289425 98352978310601601935467069)
        ·
          refine ⟨36882366866475600725800151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98352978310601601935467069 36882366866475600725800151)
          ·
            refine ⟨55323550299713401088700227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36882366866475600725800151 55323550299713401088700227)
            ·
              refine ⟨82985325449570101633050341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55323550299713401088700227 82985325449570101633050341)
              ·
                refine ⟨15559748521794394056196939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82985325449570101633050341 15559748521794394056196939)
                ·
                  refine ⟨23339622782691591084295409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15559748521794394056196939 23339622782691591084295409)
                  ·
                    refine ⟨17504717087018693313221557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23339622782691591084295409 17504717087018693313221557)
                    ·
                      refine ⟨1641067226908002498114521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17504717087018693313221557 1641067226908002498114521)
                      ·
                        rfl

theorem cell23_3195967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_3195967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195967 prefixEnd_3195967 := by exact prefixLift 3195967
  have htrace : WordTrace (prefixWord ++ tailWord_3195967) baseStart_3195967 baseEnd_3195967 := by
    simpa [prefixWord, tailWord_3195967, baseEnd_3195967] using wordTrace_append hprefix tailTrace_3195967
  have hstable : (prefixWord ++ tailWord_3195967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195967).length < 2 ^ (prefixWord ++ tailWord_3195967).sum := by decide
  have hdescent : baseEnd_3195967 < baseStart_3195967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195977 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3195977 : Nat := 118140960795 + 3195977 * 2 ^ 59
def prefixEnd_3195977 : Nat := 4983230072969 + 3 ^ 40 * 3195977 * 2
def baseEnd_3195977 : Nat := 1641072361714547458989475

theorem tailTrace_3195977 : CollatzResearch.WordTrace tailWord_3195977 prefixEnd_3195977 1641072361714547458989475 := by
  unfold tailWord_3195977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116566857542528633261010185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77711238361685755507340123 116566857542528633261010185)
  ·
    refine ⟨87425143156896474945757639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116566857542528633261010185 87425143156896474945757639)
    ·
      refine ⟨131137714735344712418636459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87425143156896474945757639 131137714735344712418636459)
      ·
        refine ⟨196706572103017068627954689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131137714735344712418636459 196706572103017068627954689)
        ·
          refine ⟨147529929077262801470966017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196706572103017068627954689 147529929077262801470966017)
          ·
            refine ⟨110647446807947101103224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147529929077262801470966017 110647446807947101103224513)
            ·
              refine ⟨82985585105960325827418385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110647446807947101103224513 82985585105960325827418385)
              ·
                refine ⟨62239188829470244370563789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82985585105960325827418385 62239188829470244370563789)
                ·
                  refine ⟨23339695811051341638961421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62239188829470244370563789 23339695811051341638961421)
                  ·
                    refine ⟨8752385929144253114610533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23339695811051341638961421 8752385929144253114610533)
                    ·
                      refine ⟨1641072361714547458989475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8752385929144253114610533 1641072361714547458989475)
                      ·
                        rfl

theorem cell23_3195977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3195977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3195977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3195977 prefixEnd_3195977 := by exact prefixLift 3195977
  have htrace : WordTrace (prefixWord ++ tailWord_3195977) baseStart_3195977 baseEnd_3195977 := by
    simpa [prefixWord, tailWord_3195977, baseEnd_3195977] using wordTrace_append hprefix tailTrace_3195977
  have hstable : (prefixWord ++ tailWord_3195977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195977).length < 2 ^ (prefixWord ++ tailWord_3195977).sum := by decide
  have hdescent : baseEnd_3195977 < baseStart_3195977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196004 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_3196004 : Nat := 118140960795 + 3196004 * 2 ^ 59
def prefixEnd_3196004 : Nat := 4983230072969 + 3 ^ 40 * 3196004 * 2
def baseEnd_3196004 : Nat := 547028741897406284450617

theorem tailTrace_3196004 : CollatzResearch.WordTrace tailWord_3196004 prefixEnd_3196004 547028741897406284450617 := by
  unfold tailWord_3196004
  simp only [CollatzResearch.WordTrace]
  refine ⟨58283921156715408436121533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77711894875620544581495377 58283921156715408436121533)
  ·
    refine ⟨21856470433768278163545575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58283921156715408436121533 21856470433768278163545575)
    ·
      refine ⟨32784705650652417245318363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21856470433768278163545575 32784705650652417245318363)
      ·
        refine ⟨49177058475978625867977545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32784705650652417245318363 49177058475978625867977545)
        ·
          refine ⟨36882793856983969400983159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49177058475978625867977545 36882793856983969400983159)
          ·
            refine ⟨55324190785475954101474739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36882793856983969400983159 55324190785475954101474739)
            ·
              refine ⟨82986286178213931152212109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55324190785475954101474739 82986286178213931152212109)
              ·
                refine ⟨31119857316830224182079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82986286178213931152212109 31119857316830224182079541)
                ·
                  refine ⟨2917486623452833517069957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31119857316830224182079541 2917486623452833517069957)
                  ·
                    refine ⟨547028741897406284450617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2917486623452833517069957 547028741897406284450617)
                    ·
                      rfl

theorem cell23_3196004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_3196004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196004 prefixEnd_3196004 := by exact prefixLift 3196004
  have htrace : WordTrace (prefixWord ++ tailWord_3196004) baseStart_3196004 baseEnd_3196004 := by
    simpa [prefixWord, tailWord_3196004, baseEnd_3196004] using wordTrace_append hprefix tailTrace_3196004
  have hstable : (prefixWord ++ tailWord_3196004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196004).length < 2 ^ (prefixWord ++ tailWord_3196004).sum := by decide
  have hdescent : baseEnd_3196004 < baseStart_3196004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196008 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3196008 : Nat := 118140960795 + 3196008 * 2 ^ 59
def prefixEnd_3196008 : Nat := 4983230072969 + 3 ^ 40 * 3196008 * 2
def baseEnd_3196008 : Nat := 547029426538278945900611

theorem tailTrace_3196008 : CollatzResearch.WordTrace tailWord_3196008 prefixEnd_3196008 547029426538278945900611 := by
  unfold tailWord_3196008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58283994102708162777694339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77711992136944217036925785 58283994102708162777694339)
  ·
    refine ⟨87425991154062244166541509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58283994102708162777694339 87425991154062244166541509)
    ·
      refine ⟨16392373341386670781226533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87425991154062244166541509 16392373341386670781226533)
      ·
        refine ⟨3073570001510000771479975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16392373341386670781226533 3073570001510000771479975)
        ·
          refine ⟨4610355002265001157219963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073570001510000771479975 4610355002265001157219963)
          ·
            refine ⟨6915532503397501735829945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610355002265001157219963 6915532503397501735829945)
            ·
              refine ⟨5186649377548126301872459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6915532503397501735829945 5186649377548126301872459)
              ·
                refine ⟨7779974066322189452808689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186649377548126301872459 7779974066322189452808689)
                ·
                  refine ⟨5834980549741642089606517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779974066322189452808689 5834980549741642089606517)
                  ·
                    refine ⟨547029426538278945900611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5834980549741642089606517 547029426538278945900611)
                    ·
                      rfl

theorem cell23_3196008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3196008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196008 prefixEnd_3196008 := by exact prefixLift 3196008
  have htrace : WordTrace (prefixWord ++ tailWord_3196008) baseStart_3196008 baseEnd_3196008 := by
    simpa [prefixWord, tailWord_3196008, baseEnd_3196008] using wordTrace_append hprefix tailTrace_3196008
  have hstable : (prefixWord ++ tailWord_3196008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196008).length < 2 ^ (prefixWord ++ tailWord_3196008).sum := by decide
  have hdescent : baseEnd_3196008 < baseStart_3196008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196017 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 8]
def baseStart_3196017 : Nat := 118140960795 + 3196017 * 2 ^ 59
def prefixEnd_3196017 : Nat := 4983230072969 + 3 ^ 40 * 3196017 * 2
def baseEnd_3196017 : Nat := 182343655660080811387699

theorem tailTrace_3196017 : CollatzResearch.WordTrace tailWord_3196017 prefixEnd_3196017 182343655660080811387699 := by
  unfold tailWord_3196017
  simp only [CollatzResearch.WordTrace]
  refine ⟨116568316462383720092466305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77712210974922480061644203 116568316462383720092466305)
  ·
    refine ⟨87426237346787790069349729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116568316462383720092466305 87426237346787790069349729)
    ·
      refine ⟨65569678010090842552012297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87426237346787790069349729 65569678010090842552012297)
      ·
        refine ⟨49177258507568131914009223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65569678010090842552012297 49177258507568131914009223)
        ·
          refine ⟨73765887761352197871013835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49177258507568131914009223 73765887761352197871013835)
          ·
            refine ⟨110648831642028296806520753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73765887761352197871013835 110648831642028296806520753)
            ·
              refine ⟨82986623731521222604890565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110648831642028296806520753 82986623731521222604890565)
              ·
                refine ⟨15559991949660229238416981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82986623731521222604890565 15559991949660229238416981)
                ·
                  refine ⟨182343655660080811387699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15559991949660229238416981 182343655660080811387699)
                  ·
                    rfl

theorem cell23_3196017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_3196017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196017 prefixEnd_3196017 := by exact prefixLift 3196017
  have htrace : WordTrace (prefixWord ++ tailWord_3196017) baseStart_3196017 baseEnd_3196017 := by
    simpa [prefixWord, tailWord_3196017, baseEnd_3196017] using wordTrace_append hprefix tailTrace_3196017
  have hstable : (prefixWord ++ tailWord_3196017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196017).length < 2 ^ (prefixWord ++ tailWord_3196017).sum := by decide
  have hdescent : baseEnd_3196017 < baseStart_3196017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196064 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_3196064 : Nat := 118140960795 + 3196064 * 2 ^ 59
def prefixEnd_3196064 : Nat := 4983230072969 + 3 ^ 40 * 3196064 * 2
def baseEnd_3196064 : Nat := 547039011510496206200525

theorem tailTrace_3196064 : CollatzResearch.WordTrace tailWord_3196064 prefixEnd_3196064 547039011510496206200525 := by
  unfold tailWord_3196064
  simp only [CollatzResearch.WordTrace]
  refine ⟨58285015346606723559713623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77713353795475631412951497 58285015346606723559713623)
  ·
    refine ⟨87427523019910085339570435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58285015346606723559713623 87427523019910085339570435)
    ·
      refine ⟨131141284529865128009355653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87427523019910085339570435 131141284529865128009355653)
      ·
        refine ⟨24588990849349711501754185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131141284529865128009355653 24588990849349711501754185)
        ·
          refine ⟨18441743137012283626315639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24588990849349711501754185 18441743137012283626315639)
          ·
            refine ⟨27662614705518425439473459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18441743137012283626315639 27662614705518425439473459)
            ·
              refine ⟨41493922058277638159210189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27662614705518425439473459 41493922058277638159210189)
              ·
                refine ⟨15560220771854114309703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41493922058277638159210189 15560220771854114309703821)
                ·
                  refine ⟨5835082789445292866138933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15560220771854114309703821 5835082789445292866138933)
                  ·
                    refine ⟨547039011510496206200525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5835082789445292866138933 547039011510496206200525)
                    ·
                      rfl

theorem cell23_3196064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_3196064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196064 prefixEnd_3196064 := by exact prefixLift 3196064
  have htrace : WordTrace (prefixWord ++ tailWord_3196064) baseStart_3196064 baseEnd_3196064 := by
    simpa [prefixWord, tailWord_3196064, baseEnd_3196064] using wordTrace_append hprefix tailTrace_3196064
  have hstable : (prefixWord ++ tailWord_3196064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196064).length < 2 ^ (prefixWord ++ tailWord_3196064).sum := by decide
  have hdescent : baseEnd_3196064 < baseStart_3196064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196104 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3196104 : Nat := 118140960795 + 3196104 * 2 ^ 59
def prefixEnd_3196104 : Nat := 4983230072969 + 3 ^ 40 * 3196104 * 2
def baseEnd_3196104 : Nat := 1641137573757668462101391

theorem tailTrace_3196104 : CollatzResearch.WordTrace tailWord_3196104 prefixEnd_3196104 1641137573757668462101391 := by
  unfold tailWord_3196104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58285744806534266975441683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77714326408712355967255577 58285744806534266975441683)
  ·
    refine ⟨87428617209801400463162525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58285744806534266975441683 87428617209801400463162525)
    ·
      refine ⟨32785731453675525173685947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87428617209801400463162525 32785731453675525173685947)
      ·
        refine ⟨49178597180513287760528921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32785731453675525173685947 49178597180513287760528921)
        ·
          refine ⟨36883947885384965820396691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49178597180513287760528921 36883947885384965820396691)
          ·
            refine ⟨55325921828077448730595037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36883947885384965820396691 55325921828077448730595037)
            ·
              refine ⟨20747220685529043273973139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55325921828077448730595037 20747220685529043273973139)
              ·
                refine ⟨31120831028293564910959709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20747220685529043273973139 31120831028293564910959709)
                ·
                  refine ⟨11670311635610086841609891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31120831028293564910959709 11670311635610086841609891)
                  ·
                    refine ⟨17505467453415130262414837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11670311635610086841609891 17505467453415130262414837)
                    ·
                      refine ⟨1641137573757668462101391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17505467453415130262414837 1641137573757668462101391)
                      ·
                        rfl

theorem cell23_3196104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3196104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196104 prefixEnd_3196104 := by exact prefixLift 3196104
  have htrace : WordTrace (prefixWord ++ tailWord_3196104) baseStart_3196104 baseEnd_3196104 := by
    simpa [prefixWord, tailWord_3196104, baseEnd_3196104] using wordTrace_append hprefix tailTrace_3196104
  have hstable : (prefixWord ++ tailWord_3196104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196104).length < 2 ^ (prefixWord ++ tailWord_3196104).sum := by decide
  have hdescent : baseEnd_3196104 < baseStart_3196104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196138 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3196138 : Nat := 118140960795 + 3196138 * 2 ^ 59
def prefixEnd_3196138 : Nat := 4983230072969 + 3 ^ 40 * 3196138 * 2
def baseEnd_3196138 : Nat := 1641155032099921329076235

theorem tailTrace_3196138 : CollatzResearch.WordTrace tailWord_3196138 prefixEnd_3196138 1641155032099921329076235 := by
  unfold tailWord_3196138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143182423736339439405267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77715153129963571838414045 29143182423736339439405267)
  ·
    refine ⟨43714773635604509159107901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29143182423736339439405267 43714773635604509159107901)
    ·
      refine ⟨16393040113351690934665463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43714773635604509159107901 16393040113351690934665463)
      ·
        refine ⟨24589560170027536401998195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16393040113351690934665463 24589560170027536401998195)
        ·
          refine ⟨36884340255041304602997293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24589560170027536401998195 36884340255041304602997293)
          ·
            refine ⟨13831627595640489226123985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36884340255041304602997293 13831627595640489226123985)
            ·
              refine ⟨10373720696730366919592989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13831627595640489226123985 10373720696730366919592989)
              ·
                refine ⟨3890145261273887594847371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10373720696730366919592989 3890145261273887594847371)
                ·
                  refine ⟨5835217891910831392271057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890145261273887594847371 5835217891910831392271057)
                  ·
                    refine ⟨4376413418933123544203293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835217891910831392271057 4376413418933123544203293)
                    ·
                      refine ⟨1641155032099921329076235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376413418933123544203293 1641155032099921329076235)
                      ·
                        rfl

theorem cell23_3196138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3196138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196138 prefixEnd_3196138 := by exact prefixLift 3196138
  have htrace : WordTrace (prefixWord ++ tailWord_3196138) baseStart_3196138 baseEnd_3196138 := by
    simpa [prefixWord, tailWord_3196138, baseEnd_3196138] using wordTrace_append hprefix tailTrace_3196138
  have hstable : (prefixWord ++ tailWord_3196138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196138).length < 2 ^ (prefixWord ++ tailWord_3196138).sum := by decide
  have hdescent : baseEnd_3196138 < baseStart_3196138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196141 : List Nat := [1, 5, 1, 2, 2, 3, 9]
def baseStart_3196141 : Nat := 118140960795 + 3196141 * 2 ^ 59
def prefixEnd_3196141 : Nat := 4983230072969 + 3 ^ 40 * 3196141 * 2
def baseEnd_3196141 : Nat := 20261192253603516263441

theorem tailTrace_3196141 : CollatzResearch.WordTrace tailWord_3196141 prefixEnd_3196141 20261192253603516263441 := by
  unfold tailWord_3196141
  simp only [CollatzResearch.WordTrace]
  refine ⟨116572839113934489269980277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77715226075956326179986851 116572839113934489269980277)
  ·
    refine ⟨10928703666931358369060651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116572839113934489269980277 10928703666931358369060651)
    ·
      refine ⟨16393055500397037553590977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10928703666931358369060651 16393055500397037553590977)
      ·
        refine ⟨12294791625297778165193233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16393055500397037553590977 12294791625297778165193233)
        ·
          refine ⟨9221093718973333623894925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12294791625297778165193233 9221093718973333623894925)
          ·
            refine ⟨3457910144615000108960597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9221093718973333623894925 3457910144615000108960597)
            ·
              refine ⟨20261192253603516263441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3457910144615000108960597 20261192253603516263441)
              ·
                rfl

theorem cell23_3196141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 9].length) (baseStart_3196141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196141 prefixEnd_3196141 := by exact prefixLift 3196141
  have htrace : WordTrace (prefixWord ++ tailWord_3196141) baseStart_3196141 baseEnd_3196141 := by
    simpa [prefixWord, tailWord_3196141, baseEnd_3196141] using wordTrace_append hprefix tailTrace_3196141
  have hstable : (prefixWord ++ tailWord_3196141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196141).length < 2 ^ (prefixWord ++ tailWord_3196141).sum := by decide
  have hdescent : baseEnd_3196141 < baseStart_3196141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196154 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3196154 : Nat := 118140960795 + 3196154 * 2 ^ 59
def prefixEnd_3196154 : Nat := 4983230072969 + 3 ^ 40 * 3196154 * 2
def baseEnd_3196154 : Nat := 547054415930131088825387

theorem tailTrace_3196154 : CollatzResearch.WordTrace tailWord_3196154 prefixEnd_3196154 547054415930131088825387 := by
  unfold tailWord_3196154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143328315721848122550879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77715542175258261660135677 29143328315721848122550879)
  ·
    refine ⟨43714992473582772183826319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29143328315721848122550879 43714992473582772183826319)
    ·
      refine ⟨65572488710374158275739479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43714992473582772183826319 65572488710374158275739479)
      ·
        refine ⟨98358733065561237413609219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65572488710374158275739479 98358733065561237413609219)
        ·
          refine ⟨147538099598341856120413829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98358733065561237413609219 147538099598341856120413829)
          ·
            refine ⟨27663393674689098022577593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147538099598341856120413829 27663393674689098022577593)
            ·
              refine ⟨20747545256016823516933195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27663393674689098022577593 20747545256016823516933195)
              ·
                refine ⟨31121317884025235275399793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20747545256016823516933195 31121317884025235275399793)
                ·
                  refine ⟨23340988413018926456549845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31121317884025235275399793 23340988413018926456549845)
                  ·
                    refine ⟨547054415930131088825387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23340988413018926456549845 547054415930131088825387)
                    ·
                      rfl

theorem cell23_3196154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3196154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196154 prefixEnd_3196154 := by exact prefixLift 3196154
  have htrace : WordTrace (prefixWord ++ tailWord_3196154) baseStart_3196154 baseEnd_3196154 := by
    simpa [prefixWord, tailWord_3196154, baseEnd_3196154] using wordTrace_append hprefix tailTrace_3196154
  have hstable : (prefixWord ++ tailWord_3196154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196154).length < 2 ^ (prefixWord ++ tailWord_3196154).sum := by decide
  have hdescent : baseEnd_3196154 < baseStart_3196154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196202 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3196202 : Nat := 118140960795 + 3196202 * 2 ^ 59
def prefixEnd_3196202 : Nat := 4983230072969 + 3 ^ 40 * 3196202 * 2
def baseEnd_3196202 : Nat := 1641187894861809078675941

theorem tailTrace_3196202 : CollatzResearch.WordTrace tailWord_3196202 prefixEnd_3196202 1641187894861809078675941 := by
  unfold tailWord_3196202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143765991678374171987715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77716709311142331125300573 29143765991678374171987715)
  ·
    refine ⟨43715648987517561257981573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29143765991678374171987715 43715648987517561257981573)
    ·
      refine ⟨8196684185159542735871545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43715648987517561257981573 8196684185159542735871545)
      ·
        refine ⟨6147513138869657051903659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8196684185159542735871545 6147513138869657051903659)
        ·
          refine ⟨9221269708304485577855489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147513138869657051903659 9221269708304485577855489)
          ·
            refine ⟨6915952281228364183391617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9221269708304485577855489 6915952281228364183391617)
            ·
              refine ⟨5186964210921273137543713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6915952281228364183391617 5186964210921273137543713)
              ·
                refine ⟨3890223158190954853157785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186964210921273137543713 3890223158190954853157785)
                ·
                  refine ⟨2917667368643216139868339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3890223158190954853157785 2917667368643216139868339)
                  ·
                    refine ⟨4376501052964824209802509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2917667368643216139868339 4376501052964824209802509)
                    ·
                      refine ⟨1641187894861809078675941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376501052964824209802509 1641187894861809078675941)
                      ·
                        rfl

theorem cell23_3196202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3196202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196202 prefixEnd_3196202 := by exact prefixLift 3196202
  have htrace : WordTrace (prefixWord ++ tailWord_3196202) baseStart_3196202 baseEnd_3196202 := by
    simpa [prefixWord, tailWord_3196202, baseEnd_3196202] using wordTrace_append hprefix tailTrace_3196202
  have hstable : (prefixWord ++ tailWord_3196202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196202).length < 2 ^ (prefixWord ++ tailWord_3196202).sum := by decide
  have hdescent : baseEnd_3196202 < baseStart_3196202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196204 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3196204 : Nat := 118140960795 + 3196204 * 2 ^ 59
def prefixEnd_3196204 : Nat := 4983230072969 + 3 ^ 40 * 3196204 * 2
def baseEnd_3196204 : Nat := 1641188921823118070850931

theorem tailTrace_3196204 : CollatzResearch.WordTrace tailWord_3196204 prefixEnd_3196204 1641188921823118070850931 := by
  unfold tailWord_3196204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58287568456353125514761833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77716757941804167353015777 58287568456353125514761833)
  ·
    refine ⟨43715676342264844136071375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58287568456353125514761833 43715676342264844136071375)
    ·
      refine ⟨65573514513397266204107063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43715676342264844136071375 65573514513397266204107063)
      ·
        refine ⟨98360271770095899306160595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65573514513397266204107063 98360271770095899306160595)
        ·
          refine ⟨147540407655143848959240893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98360271770095899306160595 147540407655143848959240893)
          ·
            refine ⟨55327652870678943359715335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147540407655143848959240893 55327652870678943359715335)
            ·
              refine ⟨82991479306018415039573003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55327652870678943359715335 82991479306018415039573003)
              ·
                refine ⟨124487218959027622559359505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82991479306018415039573003 124487218959027622559359505)
                ·
                  refine ⟨93365414219270716919519629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124487218959027622559359505 93365414219270716919519629)
                  ·
                    refine ⟨35012030332226518844819861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93365414219270716919519629 35012030332226518844819861)
                    ·
                      refine ⟨1641188921823118070850931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35012030332226518844819861 1641188921823118070850931)
                      ·
                        rfl

theorem cell23_3196204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3196204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196204 prefixEnd_3196204 := by exact prefixLift 3196204
  have htrace : WordTrace (prefixWord ++ tailWord_3196204) baseStart_3196204 baseEnd_3196204 := by
    simpa [prefixWord, tailWord_3196204, baseEnd_3196204] using wordTrace_append hprefix tailTrace_3196204
  have hstable : (prefixWord ++ tailWord_3196204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196204).length < 2 ^ (prefixWord ++ tailWord_3196204).sum := by decide
  have hdescent : baseEnd_3196204 < baseStart_3196204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196211 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3]
def baseStart_3196211 : Nat := 118140960795 + 3196211 * 2 ^ 59
def prefixEnd_3196211 : Nat := 4983230072969 + 3 ^ 40 * 3196211 * 2
def baseEnd_3196211 : Nat := 1641192516187699543463399

theorem tailTrace_3196211 : CollatzResearch.WordTrace tailWord_3196211 prefixEnd_3196211 1641192516187699543463399 := by
  unfold tailWord_3196211
  simp only [CollatzResearch.WordTrace]
  refine ⟨116575392223680891225028487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77716928149120594150018991 116575392223680891225028487)
  ·
    refine ⟨174863088335521336837542731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116575392223680891225028487 174863088335521336837542731)
    ·
      refine ⟨262294632503282005256314097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174863088335521336837542731 262294632503282005256314097)
      ·
        refine ⟨196720974377461503942235573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262294632503282005256314097 196720974377461503942235573)
        ·
          refine ⟨18442591347887015994584585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196720974377461503942235573 18442591347887015994584585)
          ·
            refine ⟨13831943510915261995938439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18442591347887015994584585 13831943510915261995938439)
            ·
              refine ⟨20747915266372892993907659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13831943510915261995938439 20747915266372892993907659)
              ·
                refine ⟨31121872899559339490861489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20747915266372892993907659 31121872899559339490861489)
                ·
                  refine ⟨23341404674669504618146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31121872899559339490861489 23341404674669504618146117)
                  ·
                    refine ⟨4376513376500532115902397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23341404674669504618146117 4376513376500532115902397)
                    ·
                      refine ⟨1641192516187699543463399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376513376500532115902397 1641192516187699543463399)
                      ·
                        rfl

theorem cell23_3196211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_3196211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196211 prefixEnd_3196211 := by exact prefixLift 3196211
  have htrace : WordTrace (prefixWord ++ tailWord_3196211) baseStart_3196211 baseEnd_3196211 := by
    simpa [prefixWord, tailWord_3196211, baseEnd_3196211] using wordTrace_append hprefix tailTrace_3196211
  have hstable : (prefixWord ++ tailWord_3196211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196211).length < 2 ^ (prefixWord ++ tailWord_3196211).sum := by decide
  have hdescent : baseEnd_3196211 < baseStart_3196211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196225 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3196225 : Nat := 118140960795 + 3196225 * 2 ^ 59
def prefixEnd_3196225 : Nat := 4983230072969 + 3 ^ 40 * 3196225 * 2
def baseEnd_3196225 : Nat := 1641199704916862488688335

theorem tailTrace_3196225 : CollatzResearch.WordTrace tailWord_3196225 prefixEnd_3196225 1641199704916862488688335 := by
  unfold tailWord_3196225
  simp only [CollatzResearch.WordTrace]
  refine ⟨116575902845630171616038129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77717268563753447744025419 116575902845630171616038129)
  ·
    refine ⟨87431927134222628712028597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116575902845630171616038129 87431927134222628712028597)
    ·
      refine ⟨8196743168833371441752681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87431927134222628712028597 8196743168833371441752681)
      ·
        refine ⟨6147557376625028581314511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8196743168833371441752681 6147557376625028581314511)
        ·
          refine ⟨9221336064937542871971767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147557376625028581314511 9221336064937542871971767)
          ·
            refine ⟨13832004097406314307957651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9221336064937542871971767 13832004097406314307957651)
            ·
              refine ⟨20748006146109471461936477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13832004097406314307957651 20748006146109471461936477)
              ·
                refine ⟨7780502304791051798226179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20748006146109471461936477 7780502304791051798226179)
                ·
                  refine ⟨11670753457186577697339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780502304791051798226179 11670753457186577697339269)
                  ·
                    refine ⟨2188266273222483318251113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11670753457186577697339269 2188266273222483318251113)
                    ·
                      refine ⟨1641199704916862488688335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188266273222483318251113 1641199704916862488688335)
                      ·
                        rfl

theorem cell23_3196225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3196225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196225 prefixEnd_3196225 := by exact prefixLift 3196225
  have htrace : WordTrace (prefixWord ++ tailWord_3196225) baseStart_3196225 baseEnd_3196225 := by
    simpa [prefixWord, tailWord_3196225, baseEnd_3196225] using wordTrace_append hprefix tailTrace_3196225
  have hstable : (prefixWord ++ tailWord_3196225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196225).length < 2 ^ (prefixWord ++ tailWord_3196225).sum := by decide
  have hdescent : baseEnd_3196225 < baseStart_3196225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196231 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 7]
def baseStart_3196231 : Nat := 118140960795 + 3196231 * 2 ^ 59
def prefixEnd_3196231 : Nat := 4983230072969 + 3 ^ 40 * 3196231 * 2
def baseEnd_3196231 : Nat := 182355865088976607245923

theorem tailTrace_3196231 : CollatzResearch.WordTrace tailWord_3196231 prefixEnd_3196231 182355865088976607245923 := by
  unfold tailWord_3196231
  simp only [CollatzResearch.WordTrace]
  refine ⟨116576121683608434640756547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77717414455738956427171031 116576121683608434640756547)
  ·
    refine ⟨174864182525412651961134821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116576121683608434640756547 174864182525412651961134821)
    ·
      refine ⟨32787034223514872242712779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174864182525412651961134821 32787034223514872242712779)
      ·
        refine ⟨49180551335272308364069169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787034223514872242712779 49180551335272308364069169)
        ·
          refine ⟨36885413501454231273051877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49180551335272308364069169 36885413501454231273051877)
          ·
            refine ⟨6916015031522668363697227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36885413501454231273051877 6916015031522668363697227)
            ·
              refine ⟨10374022547284002545545841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916015031522668363697227 10374022547284002545545841)
              ·
                refine ⟨7780516910463001909159381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10374022547284002545545841 7780516910463001909159381)
                ·
                  refine ⟨182355865088976607245923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7780516910463001909159381 182355865088976607245923)
                  ·
                    rfl

theorem cell23_3196231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 7].length) (baseStart_3196231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196231 prefixEnd_3196231 := by exact prefixLift 3196231
  have htrace : WordTrace (prefixWord ++ tailWord_3196231) baseStart_3196231 baseEnd_3196231 := by
    simpa [prefixWord, tailWord_3196231, baseEnd_3196231] using wordTrace_append hprefix tailTrace_3196231
  have hstable : (prefixWord ++ tailWord_3196231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196231).length < 2 ^ (prefixWord ++ tailWord_3196231).sum := by decide
  have hdescent : baseEnd_3196231 < baseStart_3196231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196241 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_3196241 : Nat := 118140960795 + 3196241 * 2 ^ 59
def prefixEnd_3196241 : Nat := 4983230072969 + 3 ^ 40 * 3196241 * 2
def baseEnd_3196241 : Nat := 1641207920607334426088261

theorem tailTrace_3196241 : CollatzResearch.WordTrace tailWord_3196241 prefixEnd_3196241 1641207920607334426088261 := by
  unfold tailWord_3196241
  simp only [CollatzResearch.WordTrace]
  refine ⟨116576486413572206348620577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77717657609048137565747051 116576486413572206348620577)
  ·
    refine ⟨87432364810179154761465433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116576486413572206348620577 87432364810179154761465433)
    ·
      refine ⟨65574273607634366071099075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87432364810179154761465433 65574273607634366071099075)
      ·
        refine ⟨98361410411451549106648613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65574273607634366071099075 98361410411451549106648613)
        ·
          refine ⟨18442764452147165457496615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98361410411451549106648613 18442764452147165457496615)
          ·
            refine ⟨27664146678220748186244923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442764452147165457496615 27664146678220748186244923)
            ·
              refine ⟨41496220017331122279367385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27664146678220748186244923 41496220017331122279367385)
              ·
                refine ⟨31122165012998341709525539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41496220017331122279367385 31122165012998341709525539)
                ·
                  refine ⟨46683247519497512564288309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31122165012998341709525539 46683247519497512564288309)
                  ·
                    refine ⟨4376554454952891802902029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46683247519497512564288309 4376554454952891802902029)
                    ·
                      refine ⟨1641207920607334426088261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376554454952891802902029 1641207920607334426088261)
                      ·
                        rfl

theorem cell23_3196241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_3196241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196241 prefixEnd_3196241 := by exact prefixLift 3196241
  have htrace : WordTrace (prefixWord ++ tailWord_3196241) baseStart_3196241 baseEnd_3196241 := by
    simpa [prefixWord, tailWord_3196241, baseEnd_3196241] using wordTrace_append hprefix tailTrace_3196241
  have hstable : (prefixWord ++ tailWord_3196241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196241).length < 2 ^ (prefixWord ++ tailWord_3196241).sum := by decide
  have hdescent : baseEnd_3196241 < baseStart_3196241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196248 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 5]
def baseStart_3196248 : Nat := 118140960795 + 3196248 * 2 ^ 59
def prefixEnd_3196248 : Nat := 4983230072969 + 3 ^ 40 * 3196248 * 2
def baseEnd_3196248 : Nat := 182356834996879544300081

theorem tailTrace_3196248 : CollatzResearch.WordTrace tailWord_3196248 prefixEnd_3196248 182356834996879544300081 := by
  unfold tailWord_3196248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58288370862273423272062699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77717827816364564362750265 58288370862273423272062699)
  ·
    refine ⟨87432556293410134908094049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58288370862273423272062699 87432556293410134908094049)
    ·
      refine ⟨65574417220057601181070537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87432556293410134908094049 65574417220057601181070537)
      ·
        refine ⟨49180812915043200885802903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65574417220057601181070537 49180812915043200885802903)
        ·
          refine ⟨73771219372564801328704355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49180812915043200885802903 73771219372564801328704355)
          ·
            refine ⟨110656829058847201993056533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73771219372564801328704355 110656829058847201993056533)
            ·
              refine ⟨5187038862133462593424525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110656829058847201993056533 5187038862133462593424525)
              ·
                refine ⟨1945139573300048472534197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187038862133462593424525 1945139573300048472534197)
                ·
                  refine ⟨182356834996879544300081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945139573300048472534197 182356834996879544300081)
                  ·
                    rfl

theorem cell23_3196248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 5].length) (baseStart_3196248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196248 prefixEnd_3196248 := by exact prefixLift 3196248
  have htrace : WordTrace (prefixWord ++ tailWord_3196248) baseStart_3196248 baseEnd_3196248 := by
    simpa [prefixWord, tailWord_3196248, baseEnd_3196248] using wordTrace_append hprefix tailTrace_3196248
  have hstable : (prefixWord ++ tailWord_3196248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196248).length < 2 ^ (prefixWord ++ tailWord_3196248).sum := by decide
  have hdescent : baseEnd_3196248 < baseStart_3196248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196253 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3196253 : Nat := 118140960795 + 3196253 * 2 ^ 59
def prefixEnd_3196253 : Nat := 4983230072969 + 3 ^ 40 * 3196253 * 2
def baseEnd_3196253 : Nat := 1641214082375188379138207

theorem tailTrace_3196253 : CollatzResearch.WordTrace tailWord_3196253 prefixEnd_3196253 1641214082375188379138207 := by
  unfold tailWord_3196253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116576924089528732398057413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77717949393019154932038275 116576924089528732398057413)
  ·
    refine ⟨21858173266786637324635765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116576924089528732398057413 21858173266786637324635765)
    ·
      refine ⟨2049203743761247249184603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21858173266786637324635765 2049203743761247249184603)
      ·
        refine ⟨3073805615641870873776905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049203743761247249184603 3073805615641870873776905)
        ·
          refine ⟨2305354211731403155332679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073805615641870873776905 2305354211731403155332679)
          ·
            refine ⟨3458031317597104732999019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305354211731403155332679 3458031317597104732999019)
            ·
              refine ⟨5187046976395657099498529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458031317597104732999019 5187046976395657099498529)
              ·
                refine ⟨3890285232296742824623897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187046976395657099498529 3890285232296742824623897)
                ·
                  refine ⟨2917713924222557118467923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3890285232296742824623897 2917713924222557118467923)
                  ·
                    refine ⟨4376570886333835677701885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2917713924222557118467923 4376570886333835677701885)
                    ·
                      refine ⟨1641214082375188379138207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376570886333835677701885 1641214082375188379138207)
                      ·
                        rfl

theorem cell23_3196253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3196253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196253 prefixEnd_3196253 := by exact prefixLift 3196253
  have htrace : WordTrace (prefixWord ++ tailWord_3196253) baseStart_3196253 baseEnd_3196253 := by
    simpa [prefixWord, tailWord_3196253, baseEnd_3196253] using wordTrace_append hprefix tailTrace_3196253
  have hstable : (prefixWord ++ tailWord_3196253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196253).length < 2 ^ (prefixWord ++ tailWord_3196253).sum := by decide
  have hdescent : baseEnd_3196253 < baseStart_3196253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196258 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3196258 : Nat := 118140960795 + 3196258 * 2 ^ 59
def prefixEnd_3196258 : Nat := 4983230072969 + 3 ^ 40 * 3196258 * 2
def baseEnd_3196258 : Nat := 1641216649778460859575683

theorem tailTrace_3196258 : CollatzResearch.WordTrace tailWord_3196258 prefixEnd_3196258 1641216649778460859575683 := by
  unfold tailWord_3196258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144276613627654562997357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77718070969673745501326285 29144276613627654562997357)
  ·
    refine ⟨10929103730110370461124009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29144276613627654562997357 10929103730110370461124009)
    ·
      refine ⟨8196827797582777845843007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10929103730110370461124009 8196827797582777845843007)
      ·
        refine ⟨12295241696374166768764511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196827797582777845843007 12295241696374166768764511)
        ·
          refine ⟨18442862544561250153146767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295241696374166768764511 18442862544561250153146767)
          ·
            refine ⟨27664293816841875229720151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442862544561250153146767 27664293816841875229720151)
            ·
              refine ⟨41496440725262812844580227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27664293816841875229720151 41496440725262812844580227)
              ·
                refine ⟨62244661087894219266870341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41496440725262812844580227 62244661087894219266870341)
                ·
                  refine ⟨11670873953980166112538189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62244661087894219266870341 11670873953980166112538189)
                  ·
                    refine ⟨4376577732742562292201821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11670873953980166112538189 4376577732742562292201821)
                    ·
                      refine ⟨1641216649778460859575683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376577732742562292201821 1641216649778460859575683)
                      ·
                        rfl

theorem cell23_3196258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3196258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196258 prefixEnd_3196258 := by exact prefixLift 3196258
  have htrace : WordTrace (prefixWord ++ tailWord_3196258) baseStart_3196258 baseEnd_3196258 := by
    simpa [prefixWord, tailWord_3196258, baseEnd_3196258] using wordTrace_append hprefix tailTrace_3196258
  have hstable : (prefixWord ++ tailWord_3196258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196258).length < 2 ^ (prefixWord ++ tailWord_3196258).sum := by decide
  have hdescent : baseEnd_3196258 < baseStart_3196258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196261 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_3196261 : Nat := 118140960795 + 3196261 * 2 ^ 59
def prefixEnd_3196261 : Nat := 4983230072969 + 3 ^ 40 * 3196261 * 2
def baseEnd_3196261 : Nat := 547072730073474782612723

theorem tailTrace_3196261 : CollatzResearch.WordTrace tailWord_3196261 prefixEnd_3196261 547072730073474782612723 := by
  unfold tailWord_3196261
  simp only [CollatzResearch.WordTrace]
  refine ⟨116577215873499749764348637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77718143915666499842899091 116577215873499749764348637)
  ·
    refine ⟨43716455952562406161630739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116577215873499749764348637 43716455952562406161630739)
    ·
      refine ⟨65574683928843609242446109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43716455952562406161630739 65574683928843609242446109)
      ·
        refine ⟨24590506473316353465917291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65574683928843609242446109 24590506473316353465917291)
        ·
          refine ⟨36885759709974530198875937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24590506473316353465917291 36885759709974530198875937)
          ·
            refine ⟨27664319782480897649156953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36885759709974530198875937 27664319782480897649156953)
            ·
              refine ⟨20748239836860673236867715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27664319782480897649156953 20748239836860673236867715)
              ·
                refine ⟨31122359755291009855301573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20748239836860673236867715 31122359755291009855301573)
                ·
                  refine ⟨5835442454117064347869045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31122359755291009855301573 5835442454117064347869045)
                  ·
                    refine ⟨547072730073474782612723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5835442454117064347869045 547072730073474782612723)
                    ·
                      rfl

theorem cell23_3196261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_3196261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196261 prefixEnd_3196261 := by exact prefixLift 3196261
  have htrace : WordTrace (prefixWord ++ tailWord_3196261) baseStart_3196261 baseEnd_3196261 := by
    simpa [prefixWord, tailWord_3196261, baseEnd_3196261] using wordTrace_append hprefix tailTrace_3196261
  have hstable : (prefixWord ++ tailWord_3196261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196261).length < 2 ^ (prefixWord ++ tailWord_3196261).sum := by decide
  have hdescent : baseEnd_3196261 < baseStart_3196261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196281 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3196281 : Nat := 118140960795 + 3196281 * 2 ^ 59
def prefixEnd_3196281 : Nat := 4983230072969 + 3 ^ 40 * 3196281 * 2
def baseEnd_3196281 : Nat := 1641228459833514269588077

theorem tailTrace_3196281 : CollatzResearch.WordTrace tailWord_3196281 prefixEnd_3196281 1641228459833514269588077 := by
  unfold tailWord_3196281
  simp only [CollatzResearch.WordTrace]
  refine ⟨116577945333427293180076697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77718630222284862120051131 116577945333427293180076697)
  ·
    refine ⟨87433459000070469885057523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116577945333427293180076697 87433459000070469885057523)
    ·
      refine ⟨131150188500105704827586285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87433459000070469885057523 131150188500105704827586285)
      ·
        refine ⟨49181320687539639310344857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131150188500105704827586285 49181320687539639310344857)
        ·
          refine ⟨36885990515654729482758643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49181320687539639310344857 36885990515654729482758643)
          ·
            refine ⟨55328985773482094224137965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36885990515654729482758643 55328985773482094224137965)
            ·
              refine ⟨20748369665055785334051737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55328985773482094224137965 20748369665055785334051737)
              ·
                refine ⟨15561277248791839000538803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20748369665055785334051737 15561277248791839000538803)
                ·
                  refine ⟨23341915873187758500808205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15561277248791839000538803 23341915873187758500808205)
                  ·
                    refine ⟨8753218452445409437803077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23341915873187758500808205 8753218452445409437803077)
                    ·
                      refine ⟨1641228459833514269588077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8753218452445409437803077 1641228459833514269588077)
                      ·
                        rfl

theorem cell23_3196281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3196281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196281 prefixEnd_3196281 := by exact prefixLift 3196281
  have htrace : WordTrace (prefixWord ++ tailWord_3196281) baseStart_3196281 baseEnd_3196281 := by
    simpa [prefixWord, tailWord_3196281, baseEnd_3196281] using wordTrace_append hprefix tailTrace_3196281
  have hstable : (prefixWord ++ tailWord_3196281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196281).length < 2 ^ (prefixWord ++ tailWord_3196281).sum := by decide
  have hdescent : baseEnd_3196281 < baseStart_3196281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196331 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3]
def baseStart_3196331 : Nat := 118140960795 + 3196331 * 2 ^ 59
def prefixEnd_3196331 : Nat := 4983230072969 + 3 ^ 40 * 3196331 * 2
def baseEnd_3196331 : Nat := 1641254133866239073962847

theorem tailTrace_3196331 : CollatzResearch.WordTrace tailWord_3196331 prefixEnd_3196331 1641254133866239073962847 := by
  unfold tailWord_3196331
  simp only [CollatzResearch.WordTrace]
  refine ⟨116579768983246151719396847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77719845988830767812931231 116579768983246151719396847)
  ·
    refine ⟨174869653474869227579095271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116579768983246151719396847 174869653474869227579095271)
    ·
      refine ⟨262304480212303841368642907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174869653474869227579095271 262304480212303841368642907)
      ·
        refine ⟨393456720318455762052964361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262304480212303841368642907 393456720318455762052964361)
        ·
          refine ⟨295092540238841821539723271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393456720318455762052964361 295092540238841821539723271)
          ·
            refine ⟨442638810358262732309584907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295092540238841821539723271 442638810358262732309584907)
            ·
              refine ⟨663958215537394098464377361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442638810358262732309584907 663958215537394098464377361)
              ·
                refine ⟨497968661653045573848283021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663958215537394098464377361 497968661653045573848283021)
                ·
                  refine ⟨186738248119892090193106133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497968661653045573848283021 186738248119892090193106133)
                  ·
                    refine ⟨4376677690309970863900925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186738248119892090193106133 4376677690309970863900925)
                    ·
                      refine ⟨1641254133866239073962847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376677690309970863900925 1641254133866239073962847)
                      ·
                        rfl

theorem cell23_3196331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].length) (baseStart_3196331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196331 prefixEnd_3196331 := by exact prefixLift 3196331
  have htrace : WordTrace (prefixWord ++ tailWord_3196331) baseStart_3196331 baseEnd_3196331 := by
    simpa [prefixWord, tailWord_3196331, baseEnd_3196331] using wordTrace_append hprefix tailTrace_3196331
  have hstable : (prefixWord ++ tailWord_3196331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196331).length < 2 ^ (prefixWord ++ tailWord_3196331).sum := by decide
  have hdescent : baseEnd_3196331 < baseStart_3196331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196425 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_3196425 : Nat := 118140960795 + 3196425 * 2 ^ 59
def prefixEnd_3196425 : Nat := 4983230072969 + 3 ^ 40 * 3196425 * 2
def baseEnd_3196425 : Nat := 1641302401047761706187415

theorem tailTrace_3196425 : CollatzResearch.WordTrace tailWord_3196425 prefixEnd_3196425 1641302401047761706187415 := by
  unfold tailWord_3196425
  simp only [CollatzResearch.WordTrace]
  refine ⟨116583197444905605773318729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77722131629937070515545819 116583197444905605773318729)
  ·
    refine ⟨87437398083679204329989047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116583197444905605773318729 87437398083679204329989047)
    ·
      refine ⟨131156097125518806494983571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87437398083679204329989047 131156097125518806494983571)
      ·
        refine ⟨196734145688278209742475357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131156097125518806494983571 196734145688278209742475357)
        ·
          refine ⟨73775304633104328653428259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196734145688278209742475357 73775304633104328653428259)
          ·
            refine ⟨110662956949656492980142389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73775304633104328653428259 110662956949656492980142389)
            ·
              refine ⟨10374652214030296216888349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110662956949656492980142389 10374652214030296216888349)
              ·
                refine ⟨3890494580261361081333131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10374652214030296216888349 3890494580261361081333131)
                ·
                  refine ⟨5835741870392041621999697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890494580261361081333131 5835741870392041621999697)
                  ·
                    refine ⟨4376806402794031216499773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835741870392041621999697 4376806402794031216499773)
                    ·
                      refine ⟨1641302401047761706187415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4376806402794031216499773 1641302401047761706187415)
                      ·
                        rfl

theorem cell23_3196425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_3196425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196425 prefixEnd_3196425 := by exact prefixLift 3196425
  have htrace : WordTrace (prefixWord ++ tailWord_3196425) baseStart_3196425 baseEnd_3196425 := by
    simpa [prefixWord, tailWord_3196425, baseEnd_3196425] using wordTrace_append hprefix tailTrace_3196425
  have hstable : (prefixWord ++ tailWord_3196425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196425).length < 2 ^ (prefixWord ++ tailWord_3196425).sum := by decide
  have hdescent : baseEnd_3196425 < baseStart_3196425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196428 : List Nat := [2, 2, 1, 2, 5, 1, 10]
def baseStart_3196428 : Nat := 118140960795 + 3196428 * 2 ^ 59
def prefixEnd_3196428 : Nat := 4983230072969 + 3 ^ 40 * 3196428 * 2
def baseEnd_3196428 : Nat := 20263011623329940672221

theorem tailTrace_3196428 : CollatzResearch.WordTrace tailWord_3196428 prefixEnd_3196428 20263011623329940672221 := by
  unfold tailWord_3196428
  simp only [CollatzResearch.WordTrace]
  refine ⟨58291653431947368642838969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77722204575929824857118625 58291653431947368642838969)
  ·
    refine ⟨43718740073960526482129227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58291653431947368642838969 43718740073960526482129227)
    ·
      refine ⟨65578110110940789723193841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43718740073960526482129227 65578110110940789723193841)
      ·
        refine ⟨49183582583205592292395381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65578110110940789723193841 49183582583205592292395381)
        ·
          refine ⟨4610960867175524277412067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49183582583205592292395381 4610960867175524277412067)
          ·
            refine ⟨6916441300763286416118101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610960867175524277412067 6916441300763286416118101)
            ·
              refine ⟨20263011623329940672221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6916441300763286416118101 20263011623329940672221)
              ·
                rfl

theorem cell23_3196428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 10].length) (baseStart_3196428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196428 prefixEnd_3196428 := by exact prefixLift 3196428
  have htrace : WordTrace (prefixWord ++ tailWord_3196428) baseStart_3196428 baseEnd_3196428 := by
    simpa [prefixWord, tailWord_3196428, baseEnd_3196428] using wordTrace_append hprefix tailTrace_3196428
  have hstable : (prefixWord ++ tailWord_3196428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196428).length < 2 ^ (prefixWord ++ tailWord_3196428).sum := by decide
  have hdescent : baseEnd_3196428 < baseStart_3196428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196462 : List Nat := [4, 1, 3, 1, 2, 3, 2, 7]
def baseStart_3196462 : Nat := 118140960795 + 3196462 * 2 ^ 59
def prefixEnd_3196462 : Nat := 4983230072969 + 3 ^ 40 * 3196462 * 2
def baseEnd_3196462 : Nat := 60789681475258446719435

theorem tailTrace_3196462 : CollatzResearch.WordTrace tailWord_3196462 prefixEnd_3196462 60789681475258446719435 := by
  unfold tailWord_3196462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573068368221445136551955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77723031297181040728277093 14573068368221445136551955)
  ·
    refine ⟨21859602552332167704827933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14573068368221445136551955 21859602552332167704827933)
    ·
      refine ⟨8197350957124562889310475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21859602552332167704827933 8197350957124562889310475)
      ·
        refine ⟨12296026435686844333965713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197350957124562889310475 12296026435686844333965713)
        ·
          refine ⟨9222019826765133250474285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12296026435686844333965713 9222019826765133250474285)
          ·
            refine ⟨3458257435036924968927857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9222019826765133250474285 3458257435036924968927857)
            ·
              refine ⟨2593693076277693726695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458257435036924968927857 2593693076277693726695893)
              ·
                refine ⟨60789681475258446719435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2593693076277693726695893 60789681475258446719435)
                ·
                  rfl

theorem cell23_3196462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_3196462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196462 prefixEnd_3196462 := by exact prefixLift 3196462
  have htrace : WordTrace (prefixWord ++ tailWord_3196462) baseStart_3196462 baseEnd_3196462 := by
    simpa [prefixWord, tailWord_3196462, baseEnd_3196462] using wordTrace_append hprefix tailTrace_3196462
  have hstable : (prefixWord ++ tailWord_3196462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196462).length < 2 ^ (prefixWord ++ tailWord_3196462).sum := by decide
  have hdescent : baseEnd_3196462 < baseStart_3196462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196535 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 5]
def baseStart_3196535 : Nat := 118140960795 + 3196535 * 2 ^ 59
def prefixEnd_3196535 : Nat := 4983230072969 + 3 ^ 40 * 3196535 * 2
def baseEnd_3196535 : Nat := 182373209324417363979101

theorem tailTrace_3196535 : CollatzResearch.WordTrace tailWord_3196535 prefixEnd_3196535 182373209324417363979101 := by
  unfold tailWord_3196535
  simp only [CollatzResearch.WordTrace]
  refine ⟨116587209474507094559823059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77724806316338063039882039 116587209474507094559823059)
  ·
    refine ⟨174880814211760641839734589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116587209474507094559823059 174880814211760641839734589)
    ·
      refine ⟨65580305329410240689900471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174880814211760641839734589 65580305329410240689900471)
      ·
        refine ⟨98370457994115361034850707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65580305329410240689900471 98370457994115361034850707)
        ·
          refine ⟨147555686991173041552276061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98370457994115361034850707 147555686991173041552276061)
          ·
            refine ⟨55333382621689890582103523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147555686991173041552276061 55333382621689890582103523)
            ·
              refine ⟨83000073932534835873155285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55333382621689890582103523 83000073932534835873155285)
              ·
                refine ⟨1945314232793785215777077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83000073932534835873155285 1945314232793785215777077)
                ·
                  refine ⟨182373209324417363979101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945314232793785215777077 182373209324417363979101)
                  ·
                    rfl

theorem cell23_3196535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 5].length) (baseStart_3196535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196535 prefixEnd_3196535 := by exact prefixLift 3196535
  have htrace : WordTrace (prefixWord ++ tailWord_3196535) baseStart_3196535 baseEnd_3196535 := by
    simpa [prefixWord, tailWord_3196535, baseEnd_3196535] using wordTrace_append hprefix tailTrace_3196535
  have hstable : (prefixWord ++ tailWord_3196535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196535).length < 2 ^ (prefixWord ++ tailWord_3196535).sum := by decide
  have hdescent : baseEnd_3196535 < baseStart_3196535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196555 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 7, 2]
def baseStart_3196555 : Nat := 118140960795 + 3196555 * 2 ^ 59
def prefixEnd_3196555 : Nat := 4983230072969 + 3 ^ 40 * 3196555 * 2
def baseEnd_3196555 : Nat := 1641369153532846197561817

theorem tailTrace_3196555 : CollatzResearch.WordTrace tailWord_3196555 prefixEnd_3196555 1641369153532846197561817 := by
  unfold tailWord_3196555
  simp only [CollatzResearch.WordTrace]
  refine ⟨116587938934434637975551119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77725292622956425317034079 116587938934434637975551119)
  ·
    refine ⟨174881908401651956963326679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116587938934434637975551119 174881908401651956963326679)
    ·
      refine ⟨262322862602477935444990019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174881908401651956963326679 262322862602477935444990019)
      ·
        refine ⟨393484293903716903167485029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262322862602477935444990019 393484293903716903167485029)
        ·
          refine ⟨73778305106946919343903443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393484293903716903167485029 73778305106946919343903443)
          ·
            refine ⟨110667457660420379015855165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73778305106946919343903443 110667457660420379015855165)
            ·
              refine ⟨41500296622657642130945687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110667457660420379015855165 41500296622657642130945687)
              ·
                refine ⟨62250444933986463196418531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41500296622657642130945687 62250444933986463196418531)
                ·
                  refine ⟨93375667400979694794627797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62250444933986463196418531 93375667400979694794627797)
                  ·
                    refine ⟨2188492204710461596749089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 93375667400979694794627797 2188492204710461596749089)
                    ·
                      refine ⟨1641369153532846197561817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188492204710461596749089 1641369153532846197561817)
                      ·
                        rfl

theorem cell23_3196555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7, 2].length) (baseStart_3196555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196555 prefixEnd_3196555 := by exact prefixLift 3196555
  have htrace : WordTrace (prefixWord ++ tailWord_3196555) baseStart_3196555 baseEnd_3196555 := by
    simpa [prefixWord, tailWord_3196555, baseEnd_3196555] using wordTrace_append hprefix tailTrace_3196555
  have hstable : (prefixWord ++ tailWord_3196555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196555).length < 2 ^ (prefixWord ++ tailWord_3196555).sum := by decide
  have hdescent : baseEnd_3196555 < baseStart_3196555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196595 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 5, 4]
def baseStart_3196595 : Nat := 118140960795 + 3196595 * 2 ^ 59
def prefixEnd_3196595 : Nat := 4983230072969 + 3 ^ 40 * 3196595 * 2
def baseEnd_3196595 : Nat := 547129897586342013687211

theorem tailTrace_3196595 : CollatzResearch.WordTrace tailWord_3196595 prefixEnd_3196595 547129897586342013687211 := by
  unfold tailWord_3196595
  simp only [CollatzResearch.WordTrace]
  refine ⟨116589397854289724807007239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77726265236193149871338159 116589397854289724807007239)
  ·
    refine ⟨174884096781434587210510859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116589397854289724807007239 174884096781434587210510859)
    ·
      refine ⟨262326145172151880815766289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174884096781434587210510859 262326145172151880815766289)
      ·
        refine ⟨196744608879113910611824717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262326145172151880815766289 196744608879113910611824717)
        ·
          refine ⟨73779228329667716479434269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196744608879113910611824717 73779228329667716479434269)
          ·
            refine ⟨27667210623625393679787851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73779228329667716479434269 27667210623625393679787851)
            ·
              refine ⟨41500815935438090519681777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27667210623625393679787851 41500815935438090519681777)
              ·
                refine ⟨31125611951578567889761333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41500815935438090519681777 31125611951578567889761333)
                ·
                  refine ⟨2918026120460490739665125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31125611951578567889761333 2918026120460490739665125)
                  ·
                    refine ⟨547129897586342013687211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918026120460490739665125 547129897586342013687211)
                    ·
                      rfl

theorem cell23_3196595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 4].length) (baseStart_3196595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196595 prefixEnd_3196595 := by exact prefixLift 3196595
  have htrace : WordTrace (prefixWord ++ tailWord_3196595) baseStart_3196595 baseEnd_3196595 := by
    simpa [prefixWord, tailWord_3196595, baseEnd_3196595] using wordTrace_append hprefix tailTrace_3196595
  have hstable : (prefixWord ++ tailWord_3196595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196595).length < 2 ^ (prefixWord ++ tailWord_3196595).sum := by decide
  have hdescent : baseEnd_3196595 < baseStart_3196595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196602 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_3196602 : Nat := 118140960795 + 3196602 * 2 ^ 59
def prefixEnd_3196602 : Nat := 4983230072969 + 3 ^ 40 * 3196602 * 2
def baseEnd_3196602 : Nat := 1641393287123607513674101

theorem tailTrace_3196602 : CollatzResearch.WordTrace tailWord_3196602 prefixEnd_3196602 1641393287123607513674101 := by
  unfold tailWord_3196602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29147413291316091250628015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77726435443509576668341373 29147413291316091250628015)
  ·
    refine ⟨43721119936974136875942023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29147413291316091250628015 43721119936974136875942023)
    ·
      refine ⟨65581679905461205313913035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721119936974136875942023 65581679905461205313913035)
      ·
        refine ⟨98372519858191807970869553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65581679905461205313913035 98372519858191807970869553)
        ·
          refine ⟨73779389893643855978152165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98372519858191807970869553 73779389893643855978152165)
          ·
            refine ⟨13833635605058222995903531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73779389893643855978152165 13833635605058222995903531)
            ·
              refine ⟨20750453407587334493855297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13833635605058222995903531 20750453407587334493855297)
              ·
                refine ⟨15562840055690500870391473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20750453407587334493855297 15562840055690500870391473)
                ·
                  refine ⟨11672130041767875652793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15562840055690500870391473 11672130041767875652793605)
                  ·
                    refine ⟨2188524382831476684898801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11672130041767875652793605 2188524382831476684898801)
                    ·
                      refine ⟨1641393287123607513674101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188524382831476684898801 1641393287123607513674101)
                      ·
                        rfl

theorem cell23_3196602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_3196602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196602 prefixEnd_3196602 := by exact prefixLift 3196602
  have htrace : WordTrace (prefixWord ++ tailWord_3196602) baseStart_3196602 baseEnd_3196602 := by
    simpa [prefixWord, tailWord_3196602, baseEnd_3196602] using wordTrace_append hprefix tailTrace_3196602
  have hstable : (prefixWord ++ tailWord_3196602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196602).length < 2 ^ (prefixWord ++ tailWord_3196602).sum := by decide
  have hdescent : baseEnd_3196602 < baseStart_3196602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196652 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_3196652 : Nat := 118140960795 + 3196652 * 2 ^ 59
def prefixEnd_3196652 : Nat := 4983230072969 + 3 ^ 40 * 3196652 * 2
def baseEnd_3196652 : Nat := 1641418961156332318048871

theorem tailTrace_3196652 : CollatzResearch.WordTrace tailWord_3196652 prefixEnd_3196652 1641418961156332318048871 := by
  unfold tailWord_3196652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295738407541611770916105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77727651210055482361221473 58295738407541611770916105)
  ·
    refine ⟨43721803805656208828187079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58295738407541611770916105 43721803805656208828187079)
    ·
      refine ⟨65582705708484313242280619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721803805656208828187079 65582705708484313242280619)
      ·
        refine ⟨98374058562726469863420929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65582705708484313242280619 98374058562726469863420929)
        ·
          refine ⟨73780543922044852397565697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98374058562726469863420929 73780543922044852397565697)
          ·
            refine ⟨55335407941533639298174273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73780543922044852397565697 55335407941533639298174273)
            ·
              refine ⟨41501555956150229473630705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55335407941533639298174273 41501555956150229473630705)
              ·
                refine ⟨31126166967112672105223029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41501555956150229473630705 31126166967112672105223029)
                ·
                  refine ⟨2918078153166813009864659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31126166967112672105223029 2918078153166813009864659)
                  ·
                    refine ⟨4377117229750219514796989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918078153166813009864659 4377117229750219514796989)
                    ·
                      refine ⟨1641418961156332318048871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4377117229750219514796989 1641418961156332318048871)
                      ·
                        rfl

theorem cell23_3196652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_3196652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196652 prefixEnd_3196652 := by exact prefixLift 3196652
  have htrace : WordTrace (prefixWord ++ tailWord_3196652) baseStart_3196652 baseEnd_3196652 := by
    simpa [prefixWord, tailWord_3196652, baseEnd_3196652] using wordTrace_append hprefix tailTrace_3196652
  have hstable : (prefixWord ++ tailWord_3196652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196652).length < 2 ^ (prefixWord ++ tailWord_3196652).sum := by decide
  have hdescent : baseEnd_3196652 < baseStart_3196652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196745 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_3196745 : Nat := 118140960795 + 3196745 * 2 ^ 59
def prefixEnd_3196745 : Nat := 4983230072969 + 3 ^ 40 * 3196745 * 2
def baseEnd_3196745 : Nat := 547155571619066818061981

theorem tailTrace_3196745 : CollatzResearch.WordTrace tailWord_3196745 prefixEnd_3196745 547155571619066818061981 := by
  unfold tailWord_3196745
  simp only [CollatzResearch.WordTrace]
  refine ⟨116594868803746300424967689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77729912535830866949978459 116594868803746300424967689)
  ·
    refine ⟨87446151602809725318725767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116594868803746300424967689 87446151602809725318725767)
    ·
      refine ⟨131169227404214587978088651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87446151602809725318725767 131169227404214587978088651)
      ·
        refine ⟨196753841106321881967132977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131169227404214587978088651 196753841106321881967132977)
        ·
          refine ⟨147565380829741411475349733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196753841106321881967132977 147565380829741411475349733)
          ·
            refine ⟨27668508905576514651628075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147565380829741411475349733 27668508905576514651628075)
            ·
              refine ⟨41502763358364771977442113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27668508905576514651628075 41502763358364771977442113)
              ·
                refine ⟨31127072518773578983081585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41502763358364771977442113 31127072518773578983081585)
                ·
                  refine ⟨23345304389080184237311189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31127072518773578983081585 23345304389080184237311189)
                  ·
                    refine ⟨547155571619066818061981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23345304389080184237311189 547155571619066818061981)
                    ·
                      rfl

theorem cell23_3196745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_3196745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196745 prefixEnd_3196745 := by exact prefixLift 3196745
  have htrace : WordTrace (prefixWord ++ tailWord_3196745) baseStart_3196745 baseEnd_3196745 := by
    simpa [prefixWord, tailWord_3196745, baseEnd_3196745] using wordTrace_append hprefix tailTrace_3196745
  have hstable : (prefixWord ++ tailWord_3196745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196745).length < 2 ^ (prefixWord ++ tailWord_3196745).sum := by decide
  have hdescent : baseEnd_3196745 < baseStart_3196745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196839 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 7]
def baseStart_3196839 : Nat := 118140960795 + 3196839 * 2 ^ 59
def prefixEnd_3196839 : Nat := 4983230072969 + 3 ^ 40 * 3196839 * 2
def baseEnd_3196839 : Nat := 182390553559858120712279

theorem tailTrace_3196839 : CollatzResearch.WordTrace tailWord_3196839 prefixEnd_3196839 182390553559858120712279 := by
  unfold tailWord_3196839
  simp only [CollatzResearch.WordTrace]
  refine ⟨116598297265405754478889571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77732198176937169652593047 116598297265405754478889571)
  ·
    refine ⟨174897445898108631718334357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116598297265405754478889571 174897445898108631718334357)
    ·
      refine ⟨8198317776473842111796923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174897445898108631718334357 8198317776473842111796923)
      ·
        refine ⟨12297476664710763167695385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198317776473842111796923 12297476664710763167695385)
        ·
          refine ⟨9223107498533072375771539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12297476664710763167695385 9223107498533072375771539)
          ·
            refine ⟨13834661247799608563657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223107498533072375771539 13834661247799608563657309)
            ·
              refine ⟨5187997967924853211371491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13834661247799608563657309 5187997967924853211371491)
              ·
                refine ⟨7781996951887279817057237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187997967924853211371491 7781996951887279817057237)
                ·
                  refine ⟨182390553559858120712279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7781996951887279817057237 182390553559858120712279)
                  ·
                    rfl

theorem cell23_3196839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 7].length) (baseStart_3196839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196839 prefixEnd_3196839 := by exact prefixLift 3196839
  have htrace : WordTrace (prefixWord ++ tailWord_3196839) baseStart_3196839 baseEnd_3196839 := by
    simpa [prefixWord, tailWord_3196839, baseEnd_3196839] using wordTrace_append hprefix tailTrace_3196839
  have hstable : (prefixWord ++ tailWord_3196839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196839).length < 2 ^ (prefixWord ++ tailWord_3196839).sum := by decide
  have hdescent : baseEnd_3196839 < baseStart_3196839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196890 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_3196890 : Nat := 118140960795 + 3196890 * 2 ^ 59
def prefixEnd_3196890 : Nat := 4983230072969 + 3 ^ 40 * 3196890 * 2
def baseEnd_3196890 : Nat := 182393463283566931874753

theorem tailTrace_3196890 : CollatzResearch.WordTrace tailWord_3196890 prefixEnd_3196890 182393463283566931874753 := by
  unfold tailWord_3196890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29150039347055247547249031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77733438258813993459330749 29150039347055247547249031)
  ·
    refine ⟨43725059020582871320873547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29150039347055247547249031 43725059020582871320873547)
    ·
      refine ⟨65587588530874306981310321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43725059020582871320873547 65587588530874306981310321)
      ·
        refine ⟨49190691398155730235982741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65587588530874306981310321 49190691398155730235982741)
        ·
          refine ⟨2305813659288549854811691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49190691398155730235982741 2305813659288549854811691)
          ·
            refine ⟨3458720488932824782217537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305813659288549854811691 3458720488932824782217537)
            ·
              refine ⟨2594040366699618586663153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458720488932824782217537 2594040366699618586663153)
              ·
                refine ⟨1945530275024713939997365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594040366699618586663153 1945530275024713939997365)
                ·
                  refine ⟨182393463283566931874753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945530275024713939997365 182393463283566931874753)
                  ·
                    rfl

theorem cell23_3196890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_3196890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196890 prefixEnd_3196890 := by exact prefixLift 3196890
  have htrace : WordTrace (prefixWord ++ tailWord_3196890) baseStart_3196890 baseEnd_3196890 := by
    simpa [prefixWord, tailWord_3196890, baseEnd_3196890] using wordTrace_append hprefix tailTrace_3196890
  have hstable : (prefixWord ++ tailWord_3196890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196890).length < 2 ^ (prefixWord ++ tailWord_3196890).sum := by decide
  have hdescent : baseEnd_3196890 < baseStart_3196890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196906 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_3196906 : Nat := 118140960795 + 3196906 * 2 ^ 59
def prefixEnd_3196906 : Nat := 4983230072969 + 3 ^ 40 * 3196906 * 2
def baseEnd_3196906 : Nat := 1641549385242574324272703

theorem tailTrace_3196906 : CollatzResearch.WordTrace tailWord_3196906 prefixEnd_3196906 1641549385242574324272703 := by
  unfold tailWord_3196906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29150185239040756230394643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77733827304108683281052381 29150185239040756230394643)
  ·
    refine ⟨43725277858561134345591965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29150185239040756230394643 43725277858561134345591965)
    ·
      refine ⟨16396979196960425379596987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43725277858561134345591965 16396979196960425379596987)
      ·
        refine ⟨24595468795440638069395481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16396979196960425379596987 24595468795440638069395481)
        ·
          refine ⟨18446601596580478552046611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24595468795440638069395481 18446601596580478552046611)
          ·
            refine ⟨27669902394870717828069917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18446601596580478552046611 27669902394870717828069917)
            ·
              refine ⟨10376213398076519185526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27669902394870717828069917 10376213398076519185526219)
              ·
                refine ⟨15564320097114778778289329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376213398076519185526219 15564320097114778778289329)
                ·
                  refine ⟨11673240072836084083716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15564320097114778778289329 11673240072836084083716997)
                  ·
                    refine ⟨2188732513656765765696937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11673240072836084083716997 2188732513656765765696937)
                    ·
                      refine ⟨1641549385242574324272703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188732513656765765696937 1641549385242574324272703)
                      ·
                        rfl

theorem cell23_3196906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_3196906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196906 prefixEnd_3196906 := by exact prefixLift 3196906
  have htrace : WordTrace (prefixWord ++ tailWord_3196906) baseStart_3196906 baseEnd_3196906 := by
    simpa [prefixWord, tailWord_3196906, baseEnd_3196906] using wordTrace_append hprefix tailTrace_3196906
  have hstable : (prefixWord ++ tailWord_3196906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196906).length < 2 ^ (prefixWord ++ tailWord_3196906).sum := by decide
  have hdescent : baseEnd_3196906 < baseStart_3196906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196933 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_3196933 : Nat := 118140960795 + 3196933 * 2 ^ 59
def prefixEnd_3196933 : Nat := 4983230072969 + 3 ^ 40 * 3196933 * 2
def baseEnd_3196933 : Nat := 547187749740081906211693

theorem tailTrace_3196933 : CollatzResearch.WordTrace tailWord_3196933 prefixEnd_3196933 547187749740081906211693 := by
  unfold tailWord_3196933
  simp only [CollatzResearch.WordTrace]
  refine ⟨116601725727065208532811453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77734483818043472355207635 116601725727065208532811453)
  ·
    refine ⟨43725647147649453199804295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116601725727065208532811453 43725647147649453199804295)
    ·
      refine ⟨65588470721474179799706443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43725647147649453199804295 65588470721474179799706443)
      ·
        refine ⟨98382706082211269699559665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65588470721474179799706443 98382706082211269699559665)
        ·
          refine ⟨73787029561658452274669749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98382706082211269699559665 73787029561658452274669749)
          ·
            refine ⟨6917534021405479900750289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73787029561658452274669749 6917534021405479900750289)
            ·
              refine ⟨5188150516054109925562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917534021405479900750289 5188150516054109925562717)
              ·
                refine ⟨1945556443520291222086019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188150516054109925562717 1945556443520291222086019)
                ·
                  refine ⟨2918334665280436833129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945556443520291222086019 2918334665280436833129029)
                  ·
                    refine ⟨547187749740081906211693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918334665280436833129029 547187749740081906211693)
                    ·
                      rfl

theorem cell23_3196933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_3196933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196933 prefixEnd_3196933 := by exact prefixLift 3196933
  have htrace : WordTrace (prefixWord ++ tailWord_3196933) baseStart_3196933 baseEnd_3196933 := by
    simpa [prefixWord, tailWord_3196933, baseEnd_3196933] using wordTrace_append hprefix tailTrace_3196933
  have hstable : (prefixWord ++ tailWord_3196933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196933).length < 2 ^ (prefixWord ++ tailWord_3196933).sum := by decide
  have hdescent : baseEnd_3196933 < baseStart_3196933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196976 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_3196976 : Nat := 118140960795 + 3196976 * 2 ^ 59
def prefixEnd_3196976 : Nat := 4983230072969 + 3 ^ 40 * 3196976 * 2
def baseEnd_3196976 : Nat := 547195109629463016799127

theorem tailTrace_3196976 : CollatzResearch.WordTrace tailWord_3196976 prefixEnd_3196976 547195109629463016799127 := by
  unfold tailWord_3196976
  simp only [CollatzResearch.WordTrace]
  refine ⟨58301647032954713438313391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77735529377272951251084521 58301647032954713438313391)
  ·
    refine ⟨87452470549432070157470087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58301647032954713438313391 87452470549432070157470087)
    ·
      refine ⟨131178705824148105236205131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87452470549432070157470087 131178705824148105236205131)
      ·
        refine ⟨196768058736222157854307697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131178705824148105236205131 196768058736222157854307697)
        ·
          refine ⟨147576044052166618390730773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196768058736222157854307697 147576044052166618390730773)
          ·
            refine ⟨6917627064945310237065505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147576044052166618390730773 6917627064945310237065505)
            ·
              refine ⟨5188220298708982677799129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917627064945310237065505 5188220298708982677799129)
              ·
                refine ⟨3891165224031737008349347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188220298708982677799129 3891165224031737008349347)
                ·
                  refine ⟨5836747836047605512524021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891165224031737008349347 5836747836047605512524021)
                  ·
                    refine ⟨547195109629463016799127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5836747836047605512524021 547195109629463016799127)
                    ·
                      rfl

theorem cell23_3196976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_3196976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196976 prefixEnd_3196976 := by exact prefixLift 3196976
  have htrace : WordTrace (prefixWord ++ tailWord_3196976) baseStart_3196976 baseEnd_3196976 := by
    simpa [prefixWord, tailWord_3196976, baseEnd_3196976] using wordTrace_append hprefix tailTrace_3196976
  have hstable : (prefixWord ++ tailWord_3196976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196976).length < 2 ^ (prefixWord ++ tailWord_3196976).sum := by decide
  have hdescent : baseEnd_3196976 < baseStart_3196976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196979 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4]
def baseStart_3196979 : Nat := 118140960795 + 3196979 * 2 ^ 59
def prefixEnd_3196979 : Nat := 4983230072969 + 3 ^ 40 * 3196979 * 2
def baseEnd_3196979 : Nat := 1641586869330352538659867

theorem tailTrace_3196979 : CollatzResearch.WordTrace tailWord_3196979 prefixEnd_3196979 1641586869330352538659867 := by
  unfold tailWord_3196979
  simp only [CollatzResearch.WordTrace]
  refine ⟨116603403484898558388985991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77735602323265705592657327 116603403484898558388985991)
  ·
    refine ⟨174905105227347837583478987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116603403484898558388985991 174905105227347837583478987)
    ·
      refine ⟨262357657841021756375218481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174905105227347837583478987 262357657841021756375218481)
      ·
        refine ⟨196768243380766317281413861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262357657841021756375218481 196768243380766317281413861)
        ·
          refine ⟨36894045633893684490265099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196768243380766317281413861 36894045633893684490265099)
          ·
            refine ⟨55341068450840526735397649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36894045633893684490265099 55341068450840526735397649)
            ·
              refine ⟨41505801338130395051548237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55341068450840526735397649 41505801338130395051548237)
              ·
                refine ⟨15564675501798898144330589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41505801338130395051548237 15564675501798898144330589)
                ·
                  refine ⟨5836753313174586804123971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15564675501798898144330589 5836753313174586804123971)
                  ·
                    refine ⟨8755129969761880206185957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5836753313174586804123971 8755129969761880206185957)
                    ·
                      refine ⟨1641586869330352538659867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8755129969761880206185957 1641586869330352538659867)
                      ·
                        rfl

theorem cell23_3196979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_3196979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196979 prefixEnd_3196979 := by exact prefixLift 3196979
  have htrace : WordTrace (prefixWord ++ tailWord_3196979) baseStart_3196979 baseEnd_3196979 := by
    simpa [prefixWord, tailWord_3196979, baseEnd_3196979] using wordTrace_append hprefix tailTrace_3196979
  have hstable : (prefixWord ++ tailWord_3196979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196979).length < 2 ^ (prefixWord ++ tailWord_3196979).sum := by decide
  have hdescent : baseEnd_3196979 < baseStart_3196979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196989 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_3196989 : Nat := 118140960795 + 3196989 * 2 ^ 59
def prefixEnd_3196989 : Nat := 4983230072969 + 3 ^ 40 * 3196989 * 2
def baseEnd_3196989 : Nat := 547197334712299166511607

theorem tailTrace_3196989 : CollatzResearch.WordTrace tailWord_3196989 prefixEnd_3196989 547197334712299166511607 := by
  unfold tailWord_3196989
  simp only [CollatzResearch.WordTrace]
  refine ⟨116603768214862330096850021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77735845476574886731233347 116603768214862330096850021)
  ·
    refine ⟨21863206540286686893159379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116603768214862330096850021 21863206540286686893159379)
    ·
      refine ⟨32794809810430030339739069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863206540286686893159379 32794809810430030339739069)
      ·
        refine ⟨12298053678911261377402151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32794809810430030339739069 12298053678911261377402151)
        ·
          refine ⟨18447080518366892066103227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12298053678911261377402151 18447080518366892066103227)
          ·
            refine ⟨27670620777550338099154841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447080518366892066103227 27670620777550338099154841)
            ·
              refine ⟨20752965583162753574366131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27670620777550338099154841 20752965583162753574366131)
              ·
                refine ⟨31129448374744130361549197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20752965583162753574366131 31129448374744130361549197)
                ·
                  refine ⟨11673543140529048885580949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31129448374744130361549197 11673543140529048885580949)
                  ·
                    refine ⟨547197334712299166511607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11673543140529048885580949 547197334712299166511607)
                    ·
                      rfl

theorem cell23_3196989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_3196989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3196989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3196989 prefixEnd_3196989 := by exact prefixLift 3196989
  have htrace : WordTrace (prefixWord ++ tailWord_3196989) baseStart_3196989 baseEnd_3196989 := by
    simpa [prefixWord, tailWord_3196989, baseEnd_3196989] using wordTrace_append hprefix tailTrace_3196989
  have hstable : (prefixWord ++ tailWord_3196989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196989).length < 2 ^ (prefixWord ++ tailWord_3196989).sum := by decide
  have hdescent : baseEnd_3196989 < baseStart_3196989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197006 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3197006 : Nat := 118140960795 + 3197006 * 2 ^ 59
def prefixEnd_3197006 : Nat := 4983230072969 + 3 ^ 40 * 3197006 * 2
def baseEnd_3197006 : Nat := 547200244436007977674081

theorem tailTrace_3197006 : CollatzResearch.WordTrace tailWord_3197006 prefixEnd_3197006 547200244436007977674081 := by
  unfold tailWord_3197006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575548531975092750027359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77736258837200494666812581 14575548531975092750027359)
  ·
    refine ⟨21863322797962639125041039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14575548531975092750027359 21863322797962639125041039)
    ·
      refine ⟨32794984196943958687561559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863322797962639125041039 32794984196943958687561559)
      ·
        refine ⟨49192476295415938031342339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32794984196943958687561559 49192476295415938031342339)
        ·
          refine ⟨73788714443123907047013509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49192476295415938031342339 73788714443123907047013509)
          ·
            refine ⟨13835383958085732571315033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73788714443123907047013509 13835383958085732571315033)
            ·
              refine ⟨10376537968564299428486275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13835383958085732571315033 10376537968564299428486275)
              ·
                refine ⟨15564806952846449142729413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376537968564299428486275 15564806952846449142729413)
                ·
                  refine ⟨2918401303658709214261765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15564806952846449142729413 2918401303658709214261765)
                  ·
                    refine ⟨547200244436007977674081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918401303658709214261765 547200244436007977674081)
                    ·
                      rfl

theorem cell23_3197006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3197006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197006 prefixEnd_3197006 := by exact prefixLift 3197006
  have htrace : WordTrace (prefixWord ++ tailWord_3197006) baseStart_3197006 baseEnd_3197006 := by
    simpa [prefixWord, tailWord_3197006, baseEnd_3197006] using wordTrace_append hprefix tailTrace_3197006
  have hstable : (prefixWord ++ tailWord_3197006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197006).length < 2 ^ (prefixWord ++ tailWord_3197006).sum := by decide
  have hdescent : baseEnd_3197006 < baseStart_3197006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197063 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3197063 : Nat := 118140960795 + 3197063 * 2 ^ 59
def prefixEnd_3197063 : Nat := 4983230072969 + 3 ^ 40 * 3197063 * 2
def baseEnd_3197063 : Nat := 1641630001705330210009481

theorem tailTrace_3197063 : CollatzResearch.WordTrace tailWord_3197063 prefixEnd_3197063 1641630001705330210009481 := by
  unfold tailWord_3197063
  simp only [CollatzResearch.WordTrace]
  refine ⟨116606467216594240735043843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77737644811062827156695895 116606467216594240735043843)
  ·
    refine ⟨174909700824891361102565765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116606467216594240735043843 174909700824891361102565765)
    ·
      refine ⟨32795568904667130206731081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174909700824891361102565765 32795568904667130206731081)
      ·
        refine ⟨24596676678500347655048311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32795568904667130206731081 24596676678500347655048311)
        ·
          refine ⟨36895015017750521482572467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24596676678500347655048311 36895015017750521482572467)
          ·
            refine ⟨55342522526625782223858701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36895015017750521482572467 55342522526625782223858701)
            ·
              refine ⟨20753445947484668333947013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55342522526625782223858701 20753445947484668333947013)
              ·
                refine ⟨3891271115153375312615065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20753445947484668333947013 3891271115153375312615065)
                ·
                  refine ⟨2918453336365031484461299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3891271115153375312615065 2918453336365031484461299)
                  ·
                    refine ⟨4377680004547547226691949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918453336365031484461299 4377680004547547226691949)
                    ·
                      refine ⟨1641630001705330210009481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4377680004547547226691949 1641630001705330210009481)
                      ·
                        rfl

theorem cell23_3197063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3197063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197063 prefixEnd_3197063 := by exact prefixLift 3197063
  have htrace : WordTrace (prefixWord ++ tailWord_3197063) baseStart_3197063 baseEnd_3197063 := by
    simpa [prefixWord, tailWord_3197063, baseEnd_3197063] using wordTrace_append hprefix tailTrace_3197063
  have hstable : (prefixWord ++ tailWord_3197063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197063).length < 2 ^ (prefixWord ++ tailWord_3197063).sum := by decide
  have hdescent : baseEnd_3197063 < baseStart_3197063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197064 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3197064 : Nat := 118140960795 + 3197064 * 2 ^ 59
def prefixEnd_3197064 : Nat := 4983230072969 + 3 ^ 40 * 3197064 * 2
def baseEnd_3197064 : Nat := 1641630515185984706096977

theorem tailTrace_3197064 : CollatzResearch.WordTrace tailWord_3197064 prefixEnd_3197064 1641630515185984706096977 := by
  unfold tailWord_3197064
  simp only [CollatzResearch.WordTrace]
  refine ⟨58303251844795308952915123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77737669126393745270553497 58303251844795308952915123)
  ·
    refine ⟨87454877767192963429372685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58303251844795308952915123 87454877767192963429372685)
    ·
      refine ⟨32795579162697361286014757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87454877767192963429372685 32795579162697361286014757)
      ·
        refine ⟨6149171093005755241127767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32795579162697361286014757 6149171093005755241127767)
        ·
          refine ⟨9223756639508632861691651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149171093005755241127767 9223756639508632861691651)
          ·
            refine ⟨13835634959262949292537477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223756639508632861691651 13835634959262949292537477)
            ·
              refine ⟨2594181554861802992350777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13835634959262949292537477 2594181554861802992350777)
              ·
                refine ⟨1945636166146352244263083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594181554861802992350777 1945636166146352244263083)
                ·
                  refine ⟨2918454249219528366394625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945636166146352244263083 2918454249219528366394625)
                  ·
                    refine ⟨2188840686914646274795969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2918454249219528366394625 2188840686914646274795969)
                    ·
                      refine ⟨1641630515185984706096977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188840686914646274795969 1641630515185984706096977)
                      ·
                        rfl

theorem cell23_3197064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3197064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197064 prefixEnd_3197064 := by exact prefixLift 3197064
  have htrace : WordTrace (prefixWord ++ tailWord_3197064) baseStart_3197064 baseEnd_3197064 := by
    simpa [prefixWord, tailWord_3197064, baseEnd_3197064] using wordTrace_append hprefix tailTrace_3197064
  have hstable : (prefixWord ++ tailWord_3197064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197064).length < 2 ^ (prefixWord ++ tailWord_3197064).sum := by decide
  have hdescent : baseEnd_3197064 < baseStart_3197064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197090 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3197090 : Nat := 118140960795 + 3197090 * 2 ^ 59
def prefixEnd_3197090 : Nat := 4983230072969 + 3 ^ 40 * 3197090 * 2
def baseEnd_3197090 : Nat := 1641643865683001604371857

theorem tailTrace_3197090 : CollatzResearch.WordTrace tailWord_3197090 prefixEnd_3197090 1641643865683001604371857 := by
  unfold tailWord_3197090
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151862996874106086569181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77738301324997616230851149 29151862996874106086569181)
  ·
    refine ⟨10931948623827789782463443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29151862996874106086569181 10931948623827789782463443)
    ·
      refine ⟨16397922935741684673695165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10931948623827789782463443 16397922935741684673695165)
      ·
        refine ⟨6149221100903131752635687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16397922935741684673695165 6149221100903131752635687)
        ·
          refine ⟨9223831651354697628953531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149221100903131752635687 9223831651354697628953531)
          ·
            refine ⟨13835747477032046443430297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223831651354697628953531 13835747477032046443430297)
            ·
              refine ⟨10376810607774034832572723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13835747477032046443430297 10376810607774034832572723)
              ·
                refine ⟨15565215911661052248859085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376810607774034832572723 15565215911661052248859085)
                ·
                  refine ⟨5836955966872894593322157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15565215911661052248859085 5836955966872894593322157)
                  ·
                    refine ⟨2188858487577335472495809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5836955966872894593322157 2188858487577335472495809)
                    ·
                      refine ⟨1641643865683001604371857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188858487577335472495809 1641643865683001604371857)
                      ·
                        rfl

theorem cell23_3197090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3197090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197090 prefixEnd_3197090 := by exact prefixLift 3197090
  have htrace : WordTrace (prefixWord ++ tailWord_3197090) baseStart_3197090 baseEnd_3197090 := by
    simpa [prefixWord, tailWord_3197090, baseEnd_3197090] using wordTrace_append hprefix tailTrace_3197090
  have hstable : (prefixWord ++ tailWord_3197090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197090).length < 2 ^ (prefixWord ++ tailWord_3197090).sum := by decide
  have hdescent : baseEnd_3197090 < baseStart_3197090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197103 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 4, 2, 2]
def baseStart_3197103 : Nat := 118140960795 + 3197103 * 2 ^ 59
def prefixEnd_3197103 : Nat := 4983230072969 + 3 ^ 40 * 3197103 * 2
def baseEnd_3197103 : Nat := 1641650540931510053509297

theorem tailTrace_3197103 : CollatzResearch.WordTrace tailWord_3197103 prefixEnd_3197103 1641650540931510053509297 := by
  unfold tailWord_3197103
  simp only [CollatzResearch.WordTrace]
  refine ⟨116607926136449327566499963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77738617424299551710999975 116607926136449327566499963)
  ·
    refine ⟨174911889204673991349749945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116607926136449327566499963 174911889204673991349749945)
    ·
      refine ⟨131183916903505493512312459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174911889204673991349749945 131183916903505493512312459)
      ·
        refine ⟨196775875355258240268468689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131183916903505493512312459 196775875355258240268468689)
        ·
          refine ⟨147581906516443680201351517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196775875355258240268468689 147581906516443680201351517)
          ·
            refine ⟨55343214943666380075506819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147581906516443680201351517 55343214943666380075506819)
            ·
              refine ⟨83014822415499570113260229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55343214943666380075506819 83014822415499570113260229)
              ·
                refine ⟨15565279202906169396236293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83014822415499570113260229 15565279202906169396236293)
                ·
                  refine ⟨2918489850544906761794305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15565279202906169396236293 2918489850544906761794305)
                  ·
                    refine ⟨2188867387908680071345729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2918489850544906761794305 2188867387908680071345729)
                    ·
                      refine ⟨1641650540931510053509297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188867387908680071345729 1641650540931510053509297)
                      ·
                        rfl

theorem cell23_3197103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2, 2].length) (baseStart_3197103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197103 prefixEnd_3197103 := by exact prefixLift 3197103
  have htrace : WordTrace (prefixWord ++ tailWord_3197103) baseStart_3197103 baseEnd_3197103 := by
    simpa [prefixWord, tailWord_3197103, baseEnd_3197103] using wordTrace_append hprefix tailTrace_3197103
  have hstable : (prefixWord ++ tailWord_3197103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197103).length < 2 ^ (prefixWord ++ tailWord_3197103).sum := by decide
  have hdescent : baseEnd_3197103 < baseStart_3197103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197120 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2]
def baseStart_3197120 : Nat := 118140960795 + 3197120 * 2 ^ 59
def prefixEnd_3197120 : Nat := 4983230072969 + 3 ^ 40 * 3197120 * 2
def baseEnd_3197120 : Nat := 1641659270102636486996719

theorem tailTrace_3197120 : CollatzResearch.WordTrace tailWord_3197120 prefixEnd_3197120 1641659270102636486996719 := by
  unfold tailWord_3197120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58304273088693869734934407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77739030784925159646579209 58304273088693869734934407)
  ·
    refine ⟨87456409633040804602401611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58304273088693869734934407 87456409633040804602401611)
    ·
      refine ⟨131184614449561206903602417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87456409633040804602401611 131184614449561206903602417)
      ·
        refine ⟨98388460837170905177701813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131184614449561206903602417 98388460837170905177701813)
        ·
          refine ⟨9223918203484772360409545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98388460837170905177701813 9223918203484772360409545)
          ·
            refine ⟨6917938652613579270307159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9223918203484772360409545 6917938652613579270307159)
            ·
              refine ⟨10376907978920368905460739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917938652613579270307159 10376907978920368905460739)
              ·
                refine ⟨15565361968380553358191109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376907978920368905460739 15565361968380553358191109)
                ·
                  refine ⟨2918505369071353754660833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15565361968380553358191109 2918505369071353754660833)
                  ·
                    refine ⟨2188879026803515315995625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2918505369071353754660833 2188879026803515315995625)
                    ·
                      refine ⟨1641659270102636486996719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2188879026803515315995625 1641659270102636486996719)
                      ·
                        rfl

theorem cell23_3197120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_3197120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197120 prefixEnd_3197120 := by exact prefixLift 3197120
  have htrace : WordTrace (prefixWord ++ tailWord_3197120) baseStart_3197120 baseEnd_3197120 := by
    simpa [prefixWord, tailWord_3197120, baseEnd_3197120] using wordTrace_append hprefix tailTrace_3197120
  have hstable : (prefixWord ++ tailWord_3197120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197120).length < 2 ^ (prefixWord ++ tailWord_3197120).sum := by decide
  have hdescent : baseEnd_3197120 < baseStart_3197120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197156 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_3197156 : Nat := 118140960795 + 3197156 * 2 ^ 59
def prefixEnd_3197156 : Nat := 4983230072969 + 3 ^ 40 * 3197156 * 2
def baseEnd_3197156 : Nat := 547225918468732782048851

theorem tailTrace_3197156 : CollatzResearch.WordTrace tailWord_3197156 prefixEnd_3197156 547225918468732782048851 := by
  unfold tailWord_3197156
  simp only [CollatzResearch.WordTrace]
  refine ⟨58304929602628658809089661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77739906136838211745452881 58304929602628658809089661)
  ·
    refine ⟨21864348600985747053408623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58304929602628658809089661 21864348600985747053408623)
    ·
      refine ⟨32796522901478620580112935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21864348600985747053408623 32796522901478620580112935)
      ·
        refine ⟨49194784352217930870169403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32796522901478620580112935 49194784352217930870169403)
        ·
          refine ⟨73792176528326896305254105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49194784352217930870169403 73792176528326896305254105)
          ·
            refine ⟨55344132396245172228940579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73792176528326896305254105 55344132396245172228940579)
            ·
              refine ⟨83016198594367758343410869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55344132396245172228940579 83016198594367758343410869)
              ·
                refine ⟨7782768618221977344694769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83016198594367758343410869 7782768618221977344694769)
                ·
                  refine ⟨5837076463666483008521077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7782768618221977344694769 5837076463666483008521077)
                  ·
                    refine ⟨547225918468732782048851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5837076463666483008521077 547225918468732782048851)
                    ·
                      rfl

theorem cell23_3197156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_3197156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197156 prefixEnd_3197156 := by exact prefixLift 3197156
  have htrace : WordTrace (prefixWord ++ tailWord_3197156) baseStart_3197156 baseEnd_3197156 := by
    simpa [prefixWord, tailWord_3197156, baseEnd_3197156] using wordTrace_append hprefix tailTrace_3197156
  have hstable : (prefixWord ++ tailWord_3197156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197156).length < 2 ^ (prefixWord ++ tailWord_3197156).sum := by decide
  have hdescent : baseEnd_3197156 < baseStart_3197156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197160 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 5]
def baseStart_3197160 : Nat := 118140960795 + 3197160 * 2 ^ 59
def prefixEnd_3197160 : Nat := 4983230072969 + 3 ^ 40 * 3197160 * 2
def baseEnd_3197160 : Nat := 182408867703201814499615

theorem tailTrace_3197160 : CollatzResearch.WordTrace tailWord_3197160 prefixEnd_3197160 182408867703201814499615 := by
  unfold tailWord_3197160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58305002548621413150662467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77740003398161884200883289 58305002548621413150662467)
  ·
    refine ⟨87457503822932119725993701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58305002548621413150662467 87457503822932119725993701)
    ·
      refine ⟨16398281966799772448623819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87457503822932119725993701 16398281966799772448623819)
      ·
        refine ⟨24597422950199658672935729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16398281966799772448623819 24597422950199658672935729)
        ·
          refine ⟨18448067212649744004701797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24597422950199658672935729 18448067212649744004701797)
          ·
            refine ⟨3459012602371827000881587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18448067212649744004701797 3459012602371827000881587)
            ·
              refine ⟨5188518903557740501322381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459012602371827000881587 5188518903557740501322381)
              ·
                refine ⟨1945694588834152687995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188518903557740501322381 1945694588834152687995893)
                ·
                  refine ⟨182408867703201814499615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945694588834152687995893 182408867703201814499615)
                  ·
                    rfl

theorem cell23_3197160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 5].length) (baseStart_3197160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197160 prefixEnd_3197160 := by exact prefixLift 3197160
  have htrace : WordTrace (prefixWord ++ tailWord_3197160) baseStart_3197160 baseEnd_3197160 := by
    simpa [prefixWord, tailWord_3197160, baseEnd_3197160] using wordTrace_append hprefix tailTrace_3197160
  have hstable : (prefixWord ++ tailWord_3197160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197160).length < 2 ^ (prefixWord ++ tailWord_3197160).sum := by decide
  have hdescent : baseEnd_3197160 < baseStart_3197160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197166 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3197166 : Nat := 118140960795 + 3197166 * 2 ^ 59
def prefixEnd_3197166 : Nat := 4983230072969 + 3 ^ 40 * 3197166 * 2
def baseEnd_3197166 : Nat := 1641682890212743307021507

theorem tailTrace_3197166 : CollatzResearch.WordTrace tailWord_3197166 prefixEnd_3197166 1641682890212743307021507 := by
  unfold tailWord_3197166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576277991902636165755419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77740149290147392884028901 14576277991902636165755419)
  ·
    refine ⟨21864416987853954248633129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576277991902636165755419 21864416987853954248633129)
    ·
      refine ⟨16398312740890465686474847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21864416987853954248633129 16398312740890465686474847)
      ·
        refine ⟨24597469111335698529712271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16398312740890465686474847 24597469111335698529712271)
        ·
          refine ⟨36896203667003547794568407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24597469111335698529712271 36896203667003547794568407)
          ·
            refine ⟨55344305500505321691852611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36896203667003547794568407 55344305500505321691852611)
            ·
              refine ⟨83016458250757982537778917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55344305500505321691852611 83016458250757982537778917)
              ·
                refine ⟨15565585922017121725833547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83016458250757982537778917 15565585922017121725833547)
                ·
                  refine ⟨23348378883025682588750321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15565585922017121725833547 23348378883025682588750321)
                  ·
                    refine ⟨17511284162269261941562741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23348378883025682588750321 17511284162269261941562741)
                    ·
                      refine ⟨1641682890212743307021507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17511284162269261941562741 1641682890212743307021507)
                      ·
                        rfl

theorem cell23_3197166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3197166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197166 prefixEnd_3197166 := by exact prefixLift 3197166
  have htrace : WordTrace (prefixWord ++ tailWord_3197166) baseStart_3197166 baseEnd_3197166 := by
    simpa [prefixWord, tailWord_3197166, baseEnd_3197166] using wordTrace_append hprefix tailTrace_3197166
  have hstable : (prefixWord ++ tailWord_3197166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197166).length < 2 ^ (prefixWord ++ tailWord_3197166).sum := by decide
  have hdescent : baseEnd_3197166 < baseStart_3197166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197210 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3197210 : Nat := 118140960795 + 3197210 * 2 ^ 59
def prefixEnd_3197210 : Nat := 4983230072969 + 3 ^ 40 * 3197210 * 2
def baseEnd_3197210 : Nat := 1641705483361541134871305

theorem tailTrace_3197210 : CollatzResearch.WordTrace tailWord_3197210 prefixEnd_3197210 1641705483361541134871305 := by
  unfold tailWord_3197210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29152957186765421210161271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77741219164707789893763389 29152957186765421210161271)
  ·
    refine ⟨43729435780148131815241907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29152957186765421210161271 43729435780148131815241907)
    ·
      refine ⟨65594153670222197722862861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43729435780148131815241907 65594153670222197722862861)
      ·
        refine ⟨24597807626333324146073573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65594153670222197722862861 24597807626333324146073573)
        ·
          refine ⟨4612088929937498277388795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24597807626333324146073573 4612088929937498277388795)
          ·
            refine ⟨6918133394906247416083193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612088929937498277388795 6918133394906247416083193)
            ·
              refine ⟨5188600046179685562062395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918133394906247416083193 5188600046179685562062395)
              ·
                refine ⟨7782900069269528343093593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188600046179685562062395 7782900069269528343093593)
                ·
                  refine ⟨5837175051952146257320195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7782900069269528343093593 5837175051952146257320195)
                  ·
                    refine ⟨8755762577928219385980293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837175051952146257320195 8755762577928219385980293)
                    ·
                      refine ⟨1641705483361541134871305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8755762577928219385980293 1641705483361541134871305)
                      ·
                        rfl

theorem cell23_3197210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3197210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197210 prefixEnd_3197210 := by exact prefixLift 3197210
  have htrace : WordTrace (prefixWord ++ tailWord_3197210) baseStart_3197210 baseEnd_3197210 := by
    simpa [prefixWord, tailWord_3197210, baseEnd_3197210] using wordTrace_append hprefix tailTrace_3197210
  have hstable : (prefixWord ++ tailWord_3197210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197210).length < 2 ^ (prefixWord ++ tailWord_3197210).sum := by decide
  have hdescent : baseEnd_3197210 < baseStart_3197210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197260 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3197260 : Nat := 118140960795 + 3197260 * 2 ^ 59
def prefixEnd_3197260 : Nat := 4983230072969 + 3 ^ 40 * 3197260 * 2
def baseEnd_3197260 : Nat := 1641731157394265939246075

theorem tailTrace_3197260 : CollatzResearch.WordTrace tailWord_3197260 prefixEnd_3197260 1641731157394265939246075 := by
  unfold tailWord_3197260
  simp only [CollatzResearch.WordTrace]
  refine ⟨58306826198440271689982617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77742434931253695586643489 58306826198440271689982617)
  ·
    refine ⟨43730119648830203767486963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58306826198440271689982617 43730119648830203767486963)
    ·
      refine ⟨65595179473245305651230445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43730119648830203767486963 65595179473245305651230445)
      ·
        refine ⟨24598192302466989619211417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65595179473245305651230445 24598192302466989619211417)
        ·
          refine ⟨18448644226850242214408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24598192302466989619211417 18448644226850242214408563)
          ·
            refine ⟨27672966340275363321612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18448644226850242214408563 27672966340275363321612845)
            ·
              refine ⟨10377362377603261245604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27672966340275363321612845 10377362377603261245604817)
              ·
                refine ⟨7783021783202445934203613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10377362377603261245604817 7783021783202445934203613)
                ·
                  refine ⟨2918633168700917225326355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7783021783202445934203613 2918633168700917225326355)
                  ·
                    refine ⟨4377949753051375837989533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918633168700917225326355 4377949753051375837989533)
                    ·
                      refine ⟨1641731157394265939246075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4377949753051375837989533 1641731157394265939246075)
                      ·
                        rfl

theorem cell23_3197260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3197260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197260 prefixEnd_3197260 := by exact prefixLift 3197260
  have htrace : WordTrace (prefixWord ++ tailWord_3197260) baseStart_3197260 baseEnd_3197260 := by
    simpa [prefixWord, tailWord_3197260, baseEnd_3197260] using wordTrace_append hprefix tailTrace_3197260
  have hstable : (prefixWord ++ tailWord_3197260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197260).length < 2 ^ (prefixWord ++ tailWord_3197260).sum := by decide
  have hdescent : baseEnd_3197260 < baseStart_3197260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197280 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_3197280 : Nat := 118140960795 + 3197280 * 2 ^ 59
def prefixEnd_3197280 : Nat := 4983230072969 + 3 ^ 40 * 3197280 * 2
def baseEnd_3197280 : Nat := 547247142335785286998661

theorem tailTrace_3197280 : CollatzResearch.WordTrace tailWord_3197280 prefixEnd_3197280 547247142335785286998661 := by
  unfold tailWord_3197280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58307190928404043397846647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77742921237872057863795529 58307190928404043397846647)
  ·
    refine ⟨87460786392606065096769971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58307190928404043397846647 87460786392606065096769971)
    ·
      refine ⟨131191179588909097645154957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87460786392606065096769971 131191179588909097645154957)
      ·
        refine ⟨49196692345840911616933109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131191179588909097645154957 49196692345840911616933109)
        ·
          refine ⟨4612189907422585464087479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49196692345840911616933109 4612189907422585464087479)
          ·
            refine ⟨6918284861133878196131219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612189907422585464087479 6918284861133878196131219)
            ·
              refine ⟨10377427291700817294196829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918284861133878196131219 10377427291700817294196829)
              ·
                refine ⟨3891535234387806485323811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10377427291700817294196829 3891535234387806485323811)
                ·
                  refine ⟨5837302851581709727985717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891535234387806485323811 5837302851581709727985717)
                  ·
                    refine ⟨547247142335785286998661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5837302851581709727985717 547247142335785286998661)
                    ·
                      rfl

theorem cell23_3197280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_3197280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197280 prefixEnd_3197280 := by exact prefixLift 3197280
  have htrace : WordTrace (prefixWord ++ tailWord_3197280) baseStart_3197280 baseEnd_3197280 := by
    simpa [prefixWord, tailWord_3197280, baseEnd_3197280] using wordTrace_append hprefix tailTrace_3197280
  have hstable : (prefixWord ++ tailWord_3197280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197280).length < 2 ^ (prefixWord ++ tailWord_3197280).sum := by decide
  have hdescent : baseEnd_3197280 < baseStart_3197280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197303 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_3197303 : Nat := 118140960795 + 3197303 * 2 ^ 59
def prefixEnd_3197303 : Nat := 4983230072969 + 3 ^ 40 * 3197303 * 2
def baseEnd_3197303 : Nat := 1641753237062409271008377

theorem tailTrace_3197303 : CollatzResearch.WordTrace tailWord_3197303 prefixEnd_3197303 1641753237062409271008377 := by
  unfold tailWord_3197303
  simp only [CollatzResearch.WordTrace]
  refine ⟨116615220735724761723780563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77743480490483174482520375 116615220735724761723780563)
  ·
    refine ⟨174922831103587142585670845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116615220735724761723780563 174922831103587142585670845)
    ·
      refine ⟨65596061663845178469626567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174922831103587142585670845 65596061663845178469626567)
      ·
        refine ⟨98394092495767767704439851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65596061663845178469626567 98394092495767767704439851)
        ·
          refine ⟨147591138743651651556659777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98394092495767767704439851 147591138743651651556659777)
          ·
            refine ⟨110693354057738738667494833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147591138743651651556659777 110693354057738738667494833)
            ·
              refine ⟨83020015543304054000621125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110693354057738738667494833 83020015543304054000621125)
              ·
                refine ⟨15566252914369510125116461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83020015543304054000621125 15566252914369510125116461)
                ·
                  refine ⟨5837344842888566296918673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15566252914369510125116461 5837344842888566296918673)
                  ·
                    refine ⟨4378008632166424722689005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5837344842888566296918673 4378008632166424722689005)
                    ·
                      refine ⟨1641753237062409271008377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378008632166424722689005 1641753237062409271008377)
                      ·
                        rfl

theorem cell23_3197303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_3197303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197303 prefixEnd_3197303 := by exact prefixLift 3197303
  have htrace : WordTrace (prefixWord ++ tailWord_3197303) baseStart_3197303 baseEnd_3197303 := by
    simpa [prefixWord, tailWord_3197303, baseEnd_3197303] using wordTrace_append hprefix tailTrace_3197303
  have hstable : (prefixWord ++ tailWord_3197303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197303).length < 2 ^ (prefixWord ++ tailWord_3197303).sum := by decide
  have hdescent : baseEnd_3197303 < baseStart_3197303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197314 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3197314 : Nat := 118140960795 + 3197314 * 2 ^ 59
def prefixEnd_3197314 : Nat := 4983230072969 + 3 ^ 40 * 3197314 * 2
def baseEnd_3197314 : Nat := 547252961783202909323609

theorem tailTrace_3197314 : CollatzResearch.WordTrace tailWord_3197314 prefixEnd_3197314 547252961783202909323609 := by
  unfold tailWord_3197314
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153905484671227650607749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77743747959123273734953997 29153905484671227650607749)
  ·
    refine ⟨5466357278375855184488953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29153905484671227650607749 5466357278375855184488953)
    ·
      refine ⟨4099767958781891388366715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5466357278375855184488953 4099767958781891388366715)
      ·
        refine ⟨6149651938172837082550073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099767958781891388366715 6149651938172837082550073)
        ·
          refine ⟨4612238953629627811912555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6149651938172837082550073 4612238953629627811912555)
          ·
            refine ⟨6918358430444441717868833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612238953629627811912555 6918358430444441717868833)
            ·
              refine ⟨5188768822833331288401625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918358430444441717868833 5188768822833331288401625)
              ·
                refine ⟨3891576617124998466301219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188768822833331288401625 3891576617124998466301219)
                ·
                  refine ⟨5837364925687497699451829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891576617124998466301219 5837364925687497699451829)
                  ·
                    refine ⟨547252961783202909323609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5837364925687497699451829 547252961783202909323609)
                    ·
                      rfl

theorem cell23_3197314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3197314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197314 prefixEnd_3197314 := by exact prefixLift 3197314
  have htrace : WordTrace (prefixWord ++ tailWord_3197314) baseStart_3197314 baseEnd_3197314 := by
    simpa [prefixWord, tailWord_3197314, baseEnd_3197314] using wordTrace_append hprefix tailTrace_3197314
  have hstable : (prefixWord ++ tailWord_3197314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197314).length < 2 ^ (prefixWord ++ tailWord_3197314).sum := by decide
  have hdescent : baseEnd_3197314 < baseStart_3197314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197323 : List Nat := [1, 1, 1, 1, 4, 4, 4, 7]
def baseStart_3197323 : Nat := 118140960795 + 3197323 * 2 ^ 59
def prefixEnd_3197323 : Nat := 4983230072969 + 3 ^ 40 * 3197323 * 2
def baseEnd_3197323 : Nat := 60806055802796266398455

theorem tailTrace_3197323 : CollatzResearch.WordTrace tailWord_3197323 prefixEnd_3197323 60806055802796266398455 := by
  unfold tailWord_3197323
  simp only [CollatzResearch.WordTrace]
  refine ⟨116615950195652305139508623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77743966797101536759672415 116615950195652305139508623)
  ·
    refine ⟨174923925293478457709262935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116615950195652305139508623 174923925293478457709262935)
    ·
      refine ⟨262385887940217686563894403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174923925293478457709262935 262385887940217686563894403)
      ·
        refine ⟨393578831910326529845841605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262385887940217686563894403 393578831910326529845841605)
        ·
          refine ⟨73796030983186224346095301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393578831910326529845841605 73796030983186224346095301)
          ·
            refine ⟨13836755809347417064892869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73796030983186224346095301 13836755809347417064892869)
            ·
              refine ⟨2594391714252640699667413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13836755809347417064892869 2594391714252640699667413)
              ·
                refine ⟨60806055802796266398455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2594391714252640699667413 60806055802796266398455)
                ·
                  rfl

theorem cell23_3197323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 7].length) (baseStart_3197323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197323 prefixEnd_3197323 := by exact prefixLift 3197323
  have htrace : WordTrace (prefixWord ++ tailWord_3197323) baseStart_3197323 baseEnd_3197323 := by
    simpa [prefixWord, tailWord_3197323, baseEnd_3197323] using wordTrace_append hprefix tailTrace_3197323
  have hstable : (prefixWord ++ tailWord_3197323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197323).length < 2 ^ (prefixWord ++ tailWord_3197323).sum := by decide
  have hdescent : baseEnd_3197323 < baseStart_3197323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197333 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_3197333 : Nat := 118140960795 + 3197333 * 2 ^ 59
def prefixEnd_3197333 : Nat := 4983230072969 + 3 ^ 40 * 3197333 * 2
def baseEnd_3197333 : Nat := 1641768641482044153633239

theorem tailTrace_3197333 : CollatzResearch.WordTrace tailWord_3197333 prefixEnd_3197333 1641768641482044153633239 := by
  unfold tailWord_3197333
  simp only [CollatzResearch.WordTrace]
  refine ⟨116616314925616076847372653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77744209950410717898248435 116616314925616076847372653)
  ·
    refine ⟨43731118097106028817764745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116616314925616076847372653 43731118097106028817764745)
    ·
      refine ⟨32798338572829521613323559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43731118097106028817764745 32798338572829521613323559)
      ·
        refine ⟨49197507859244282419985339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32798338572829521613323559 49197507859244282419985339)
        ·
          refine ⟨73796261788866423629978009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49197507859244282419985339 73796261788866423629978009)
          ·
            refine ⟨55347196341649817722483507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73796261788866423629978009 55347196341649817722483507)
            ·
              refine ⟨83020794512474726583725261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55347196341649817722483507 83020794512474726583725261)
              ·
                refine ⟨31132797942178022468896973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83020794512474726583725261 31132797942178022468896973)
                ·
                  refine ⟨11674799228316758425836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31132797942178022468896973 11674799228316758425836365)
                  ·
                    refine ⟨4378049710618784409688637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11674799228316758425836365 4378049710618784409688637)
                    ·
                      refine ⟨1641768641482044153633239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378049710618784409688637 1641768641482044153633239)
                      ·
                        rfl

theorem cell23_3197333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_3197333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197333 prefixEnd_3197333 := by exact prefixLift 3197333
  have htrace : WordTrace (prefixWord ++ tailWord_3197333) baseStart_3197333 baseEnd_3197333 := by
    simpa [prefixWord, tailWord_3197333, baseEnd_3197333] using wordTrace_append hprefix tailTrace_3197333
  have hstable : (prefixWord ++ tailWord_3197333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197333).length < 2 ^ (prefixWord ++ tailWord_3197333).sum := by decide
  have hdescent : baseEnd_3197333 < baseStart_3197333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197367 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_3197367 : Nat := 118140960795 + 3197367 * 2 ^ 59
def prefixEnd_3197367 : Nat := 4983230072969 + 3 ^ 40 * 3197367 * 2
def baseEnd_3197367 : Nat := 1641786099824297020608083

theorem tailTrace_3197367 : CollatzResearch.WordTrace tailWord_3197367 prefixEnd_3197367 1641786099824297020608083 := by
  unfold tailWord_3197367
  simp only [CollatzResearch.WordTrace]
  refine ⟨116617555007492900654110355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77745036671661933769406903 116617555007492900654110355)
  ·
    refine ⟨174926332511239350981165533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116617555007492900654110355 174926332511239350981165533)
    ·
      refine ⟨65597374691714756617937075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174926332511239350981165533 65597374691714756617937075)
      ·
        refine ⟨98396062037572134926905613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65597374691714756617937075 98396062037572134926905613)
        ·
          refine ⟨36898523264089550597589605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98396062037572134926905613 36898523264089550597589605)
          ·
            refine ⟨6918473112016790737048051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36898523264089550597589605 6918473112016790737048051)
            ·
              refine ⟨10377709668025186105572077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918473112016790737048051 10377709668025186105572077)
              ·
                refine ⟨3891641125509444789589529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10377709668025186105572077 3891641125509444789589529)
                ·
                  refine ⟨2918730844132083592192147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3891641125509444789589529 2918730844132083592192147)
                  ·
                    refine ⟨4378096266198125388288221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918730844132083592192147 4378096266198125388288221)
                    ·
                      refine ⟨1641786099824297020608083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378096266198125388288221 1641786099824297020608083)
                      ·
                        rfl

theorem cell23_3197367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_3197367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197367 prefixEnd_3197367 := by exact prefixLift 3197367
  have htrace : WordTrace (prefixWord ++ tailWord_3197367) baseStart_3197367 baseEnd_3197367 := by
    simpa [prefixWord, tailWord_3197367, baseEnd_3197367] using wordTrace_append hprefix tailTrace_3197367
  have hstable : (prefixWord ++ tailWord_3197367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197367).length < 2 ^ (prefixWord ++ tailWord_3197367).sum := by decide
  have hdescent : baseEnd_3197367 < baseStart_3197367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_3197393 : Nat := 118140960795 + 3197393 * 2 ^ 59
def prefixEnd_3197393 : Nat := 4983230072969 + 3 ^ 40 * 3197393 * 2
def baseEnd_3197393 : Nat := 1641799450321313918882963

theorem tailTrace_3197393 : CollatzResearch.WordTrace tailWord_3197393 prefixEnd_3197393 1641799450321313918882963 := by
  unfold tailWord_3197393
  simp only [CollatzResearch.WordTrace]
  refine ⟨116618503305398707094556833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77745668870265804729704555 116618503305398707094556833)
  ·
    refine ⟨87463877479049030320917625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116618503305398707094556833 87463877479049030320917625)
    ·
      refine ⟨65597908109286772740688219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87463877479049030320917625 65597908109286772740688219)
      ·
        refine ⟨98396862163930159111032329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65597908109286772740688219 98396862163930159111032329)
        ·
          refine ⟨73797646622947619333274247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98396862163930159111032329 73797646622947619333274247)
          ·
            refine ⟨110696469934421428999911371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73797646622947619333274247 110696469934421428999911371)
            ·
              refine ⟨166044704901632143499867057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110696469934421428999911371 166044704901632143499867057)
              ·
                refine ⟨124533528676224107624900293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166044704901632143499867057 124533528676224107624900293)
                ·
                  refine ⟨23350036626792020179668805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124533528676224107624900293 23350036626792020179668805)
                  ·
                    refine ⟨4378131867523503783687901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23350036626792020179668805 4378131867523503783687901)
                    ·
                      refine ⟨1641799450321313918882963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378131867523503783687901 1641799450321313918882963)
                      ·
                        rfl

theorem cell23_3197393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_3197393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197393 prefixEnd_3197393 := by exact prefixLift 3197393
  have htrace : WordTrace (prefixWord ++ tailWord_3197393) baseStart_3197393 baseEnd_3197393 := by
    simpa [prefixWord, tailWord_3197393, baseEnd_3197393] using wordTrace_append hprefix tailTrace_3197393
  have hstable : (prefixWord ++ tailWord_3197393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197393).length < 2 ^ (prefixWord ++ tailWord_3197393).sum := by decide
  have hdescent : baseEnd_3197393 < baseStart_3197393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197430 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3197430 : Nat := 118140960795 + 3197430 * 2 ^ 59
def prefixEnd_3197430 : Nat := 4983230072969 + 3 ^ 40 * 3197430 * 2
def baseEnd_3197430 : Nat := 182424272122836697124477

theorem tailTrace_3197430 : CollatzResearch.WordTrace tailWord_3197430 prefixEnd_3197430 182424272122836697124477 := by
  unfold tailWord_3197430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288740800391541400853359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77746568537509774942435829 7288740800391541400853359)
  ·
    refine ⟨10933111200587312101280039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288740800391541400853359 10933111200587312101280039)
    ·
      refine ⟨16399666800880968151920059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933111200587312101280039 16399666800880968151920059)
      ·
        refine ⟨24599500201321452227880089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399666800880968151920059 24599500201321452227880089)
        ·
          refine ⟨18449625150991089170910067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24599500201321452227880089 18449625150991089170910067)
          ·
            refine ⟨27674437726486633756365101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18449625150991089170910067 27674437726486633756365101)
            ·
              refine ⟨10377914147432487658636913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27674437726486633756365101 10377914147432487658636913)
              ·
                refine ⟨7783435610574365743977685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10377914147432487658636913 7783435610574365743977685)
                ·
                  refine ⟨182424272122836697124477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7783435610574365743977685 182424272122836697124477)
                  ·
                    rfl

theorem cell23_3197430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3197430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197430 prefixEnd_3197430 := by exact prefixLift 3197430
  have htrace : WordTrace (prefixWord ++ tailWord_3197430) baseStart_3197430 baseEnd_3197430 := by
    simpa [prefixWord, tailWord_3197430, baseEnd_3197430] using wordTrace_append hprefix tailTrace_3197430
  have hstable : (prefixWord ++ tailWord_3197430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197430).length < 2 ^ (prefixWord ++ tailWord_3197430).sum := by decide
  have hdescent : baseEnd_3197430 < baseStart_3197430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197443 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 7]
def baseStart_3197443 : Nat := 118140960795 + 3197443 * 2 ^ 59
def prefixEnd_3197443 : Nat := 4983230072969 + 3 ^ 40 * 3197443 * 2
def baseEnd_3197443 : Nat := 547275041451346241085911

theorem tailTrace_3197443 : CollatzResearch.WordTrace tailWord_3197443 prefixEnd_3197443 547275041451346241085911 := by
  unfold tailWord_3197443
  simp only [CollatzResearch.WordTrace]
  refine ⟨116620326955217565633876983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77746884636811710422584655 116620326955217565633876983)
  ·
    refine ⟨174930490432826348450815475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116620326955217565633876983 174930490432826348450815475)
    ·
      refine ⟨262395735649239522676223213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174930490432826348450815475 262395735649239522676223213)
      ·
        refine ⟨98398400868464821003583705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262395735649239522676223213 98398400868464821003583705)
        ·
          refine ⟨73798800651348615752687779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98398400868464821003583705 73798800651348615752687779)
          ·
            refine ⟨110698200977022923629031669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73798800651348615752687779 110698200977022923629031669)
            ·
              refine ⟨10377956341595899090221719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110698200977022923629031669 10377956341595899090221719)
              ·
                refine ⟨15566934512393848635332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10377956341595899090221719 15566934512393848635332579)
                ·
                  refine ⟨23350401768590772952998869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15566934512393848635332579 23350401768590772952998869)
                  ·
                    refine ⟨547275041451346241085911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23350401768590772952998869 547275041451346241085911)
                    ·
                      rfl

theorem cell23_3197443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_3197443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197443 prefixEnd_3197443 := by exact prefixLift 3197443
  have htrace : WordTrace (prefixWord ++ tailWord_3197443) baseStart_3197443 baseEnd_3197443 := by
    simpa [prefixWord, tailWord_3197443, baseEnd_3197443] using wordTrace_append hprefix tailTrace_3197443
  have hstable : (prefixWord ++ tailWord_3197443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197443).length < 2 ^ (prefixWord ++ tailWord_3197443).sum := by decide
  have hdescent : baseEnd_3197443 < baseStart_3197443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197503 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 10]
def baseStart_3197503 : Nat := 118140960795 + 3197503 * 2 ^ 59
def prefixEnd_3197503 : Nat := 4983230072969 + 3 ^ 40 * 3197503 * 2
def baseEnd_3197503 : Nat := 182428437021478720945273

theorem tailTrace_3197503 : CollatzResearch.WordTrace tailWord_3197503 prefixEnd_3197503 182428437021478720945273 := by
  unfold tailWord_3197503
  simp only [CollatzResearch.WordTrace]
  refine ⟨116622515335000195881061163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77748343556666797254040775 116622515335000195881061163)
  ·
    refine ⟨174933773002500293821591745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116622515335000195881061163 174933773002500293821591745)
    ·
      refine ⟨131200329751875220366193809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174933773002500293821591745 131200329751875220366193809)
      ·
        refine ⟨98400247313906415274645357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131200329751875220366193809 98400247313906415274645357)
        ·
          refine ⟨36900092742714905727992009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98400247313906415274645357 36900092742714905727992009)
          ·
            refine ⟨27675069557036179295994007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36900092742714905727992009 27675069557036179295994007)
            ·
              refine ⟨41512604335554268943991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27675069557036179295994007 41512604335554268943991011)
              ·
                refine ⟨62268906503331403415986517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41512604335554268943991011 62268906503331403415986517)
                ·
                  refine ⟨182428437021478720945273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62268906503331403415986517 182428437021478720945273)
                  ·
                    rfl

theorem cell23_3197503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 10].length) (baseStart_3197503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197503 prefixEnd_3197503 := by exact prefixLift 3197503
  have htrace : WordTrace (prefixWord ++ tailWord_3197503) baseStart_3197503 baseEnd_3197503 := by
    simpa [prefixWord, tailWord_3197503, baseEnd_3197503] using wordTrace_append hprefix tailTrace_3197503
  have hstable : (prefixWord ++ tailWord_3197503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197503).length < 2 ^ (prefixWord ++ tailWord_3197503).sum := by decide
  have hdescent : baseEnd_3197503 < baseStart_3197503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197524 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3197524 : Nat := 118140960795 + 3197524 * 2 ^ 59
def prefixEnd_3197524 : Nat := 4983230072969 + 3 ^ 40 * 3197524 * 2
def baseEnd_3197524 : Nat := 547288905429017635448287

theorem tailTrace_3197524 : CollatzResearch.WordTrace tailWord_3197524 prefixEnd_3197524 547288905429017635448287 := by
  unfold tailWord_3197524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58311640633962058233787813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77748854178616077645050417 58311640633962058233787813)
  ·
    refine ⟨10933432618867885918835215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58311640633962058233787813 10933432618867885918835215)
    ·
      refine ⟨16400148928301828878252823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933432618867885918835215 16400148928301828878252823)
      ·
        refine ⟨24600223392452743317379235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16400148928301828878252823 24600223392452743317379235)
        ·
          refine ⟨36900335088679114976068853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24600223392452743317379235 36900335088679114976068853)
          ·
            refine ⟨3459406414563667029006455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36900335088679114976068853 3459406414563667029006455)
            ·
              refine ⟨5189109621845500543509683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459406414563667029006455 5189109621845500543509683)
              ·
                refine ⟨7783664432768250815264525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189109621845500543509683 7783664432768250815264525)
                ·
                  refine ⟨2918874162288094055724197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7783664432768250815264525 2918874162288094055724197)
                  ·
                    refine ⟨547288905429017635448287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918874162288094055724197 547288905429017635448287)
                    ·
                      rfl

theorem cell23_3197524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3197524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197524 prefixEnd_3197524 := by exact prefixLift 3197524
  have htrace : WordTrace (prefixWord ++ tailWord_3197524) baseStart_3197524 baseEnd_3197524 := by
    simpa [prefixWord, tailWord_3197524, baseEnd_3197524] using wordTrace_append hprefix tailTrace_3197524
  have hstable : (prefixWord ++ tailWord_3197524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197524).length < 2 ^ (prefixWord ++ tailWord_3197524).sum := by decide
  have hdescent : baseEnd_3197524 < baseStart_3197524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197537 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 6]
def baseStart_3197537 : Nat := 118140960795 + 3197537 * 2 ^ 59
def prefixEnd_3197537 : Nat := 4983230072969 + 3 ^ 40 * 3197537 * 2
def baseEnd_3197537 : Nat := 182430376837284595053589

theorem tailTrace_3197537 : CollatzResearch.WordTrace tailWord_3197537 prefixEnd_3197537 182430376837284595053589 := by
  unfold tailWord_3197537
  simp only [CollatzResearch.WordTrace]
  refine ⟨116623755416877019687798865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77749170277918013125199243 116623755416877019687798865)
  ·
    refine ⟨87467816562657764765849149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116623755416877019687798865 87467816562657764765849149)
    ·
      refine ⟨32800431210996661787193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87467816562657764765849149 32800431210996661787193431)
      ·
        refine ⟨49200646816494992680790147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32800431210996661787193431 49200646816494992680790147)
        ·
          refine ⟨73800970224742489021185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49200646816494992680790147 73800970224742489021185221)
          ·
            refine ⟨13837681917139216691472229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73800970224742489021185221 13837681917139216691472229)
            ·
              refine ⟨2594565359463603129651043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13837681917139216691472229 2594565359463603129651043)
              ·
                refine ⟨3891848039195404694476565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594565359463603129651043 3891848039195404694476565)
                ·
                  refine ⟨182430376837284595053589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3891848039195404694476565 182430376837284595053589)
                  ·
                    rfl

theorem cell23_3197537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_3197537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197537 prefixEnd_3197537 := by exact prefixLift 3197537
  have htrace : WordTrace (prefixWord ++ tailWord_3197537) baseStart_3197537 baseEnd_3197537 := by
    simpa [prefixWord, tailWord_3197537, baseEnd_3197537] using wordTrace_append hprefix tailTrace_3197537
  have hstable : (prefixWord ++ tailWord_3197537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197537).length < 2 ^ (prefixWord ++ tailWord_3197537).sum := by decide
  have hdescent : baseEnd_3197537 < baseStart_3197537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197614 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3197614 : Nat := 118140960795 + 3197614 * 2 ^ 59
def prefixEnd_3197614 : Nat := 4983230072969 + 3 ^ 40 * 3197614 * 2
def baseEnd_3197614 : Nat := 547304309848652518073149

theorem tailTrace_3197614 : CollatzResearch.WordTrace tailWord_3197614 prefixEnd_3197614 547304309848652518073149 := by
  unfold tailWord_3197614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578320479699757729793987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77751042558398707892234597 14578320479699757729793987)
  ·
    refine ⟨21867480719549636594690981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14578320479699757729793987 21867480719549636594690981)
    ·
      refine ⟨4100152634915556861504559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21867480719549636594690981 4100152634915556861504559)
      ·
        refine ⟨6150228952373335292256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100152634915556861504559 6150228952373335292256839)
        ·
          refine ⟨9225343428560002938385259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150228952373335292256839 9225343428560002938385259)
          ·
            refine ⟨13838015142840004407577889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225343428560002938385259 13838015142840004407577889)
            ·
              refine ⟨10378511357130003305683417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13838015142840004407577889 10378511357130003305683417)
              ·
                refine ⟨7783883517847502479262563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10378511357130003305683417 7783883517847502479262563)
                ·
                  refine ⟨11675825276771253718893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783883517847502479262563 11675825276771253718893845)
                  ·
                    refine ⟨547304309848652518073149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11675825276771253718893845 547304309848652518073149)
                    ·
                      rfl

theorem cell23_3197614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3197614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197614 prefixEnd_3197614 := by exact prefixLift 3197614
  have htrace : WordTrace (prefixWord ++ tailWord_3197614) baseStart_3197614 baseEnd_3197614 := by
    simpa [prefixWord, tailWord_3197614, baseEnd_3197614] using wordTrace_append hprefix tailTrace_3197614
  have hstable : (prefixWord ++ tailWord_3197614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197614).length < 2 ^ (prefixWord ++ tailWord_3197614).sum := by decide
  have hdescent : baseEnd_3197614 < baseStart_3197614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197621 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3197621 : Nat := 118140960795 + 3197621 * 2 ^ 59
def prefixEnd_3197621 : Nat := 4983230072969 + 3 ^ 40 * 3197621 * 2
def baseEnd_3197621 : Nat := 1641916523910539026831915

theorem tailTrace_3197621 : CollatzResearch.WordTrace tailWord_3197621 prefixEnd_3197621 1641916523910539026831915 := by
  unfold tailWord_3197621
  simp only [CollatzResearch.WordTrace]
  refine ⟨116626819148572702033856717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77751212765715134689237811 116626819148572702033856717)
  ·
    refine ⟨43735057180714763262696269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116626819148572702033856717 43735057180714763262696269)
    ·
      refine ⟨16400646442768036223511101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43735057180714763262696269 16400646442768036223511101)
      ·
        refine ⟨6150242416038013583816663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16400646442768036223511101 6150242416038013583816663)
        ·
          refine ⟨9225363624057020375724995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150242416038013583816663 9225363624057020375724995)
          ·
            refine ⟨13838045436085530563587493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225363624057020375724995 13838045436085530563587493)
            ·
              refine ⟨2594633519266036980672655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13838045436085530563587493 2594633519266036980672655)
              ·
                refine ⟨3891950278899055471008983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594633519266036980672655 3891950278899055471008983)
                ·
                  refine ⟨5837925418348583206513475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891950278899055471008983 5837925418348583206513475)
                  ·
                    refine ⟨8756888127522874809770213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837925418348583206513475 8756888127522874809770213)
                    ·
                      refine ⟨1641916523910539026831915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8756888127522874809770213 1641916523910539026831915)
                      ·
                        rfl

theorem cell23_3197621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3197621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197621 prefixEnd_3197621 := by exact prefixLift 3197621
  have htrace : WordTrace (prefixWord ++ tailWord_3197621) baseStart_3197621 baseEnd_3197621 := by
    simpa [prefixWord, tailWord_3197621, baseEnd_3197621] using wordTrace_append hprefix tailTrace_3197621
  have hstable : (prefixWord ++ tailWord_3197621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197621).length < 2 ^ (prefixWord ++ tailWord_3197621).sum := by decide
  have hdescent : baseEnd_3197621 < baseStart_3197621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197667 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3197667 : Nat := 118140960795 + 3197667 * 2 ^ 59
def prefixEnd_3197667 : Nat := 4983230072969 + 3 ^ 40 * 3197667 * 2
def baseEnd_3197667 : Nat := 1641940144020645846856703

theorem tailTrace_3197667 : CollatzResearch.WordTrace tailWord_3197667 prefixEnd_3197667 1641940144020645846856703 := by
  unfold tailWord_3197667
  simp only [CollatzResearch.WordTrace]
  refine ⟨116628496906406051890031255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77752331270937367926687503 116628496906406051890031255)
  ·
    refine ⟨174942745359609077835046883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116628496906406051890031255 174942745359609077835046883)
    ·
      refine ⟨262414118039413616752570325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174942745359609077835046883 262414118039413616752570325)
      ·
        refine ⟨6150330891548756642638367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 262414118039413616752570325 6150330891548756642638367)
        ·
          refine ⟨9225496337323134963957551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150330891548756642638367 9225496337323134963957551)
          ·
            refine ⟨13838244505984702445936327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225496337323134963957551 13838244505984702445936327)
            ·
              refine ⟨20757366758977053668904491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838244505984702445936327 20757366758977053668904491)
              ·
                refine ⟨31136050138465580503356737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20757366758977053668904491 31136050138465580503356737)
                ·
                  refine ⟨23352037603849185377517553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31136050138465580503356737 23352037603849185377517553)
                  ·
                    refine ⟨17514028202886889033138165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23352037603849185377517553 17514028202886889033138165)
                    ·
                      refine ⟨1641940144020645846856703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17514028202886889033138165 1641940144020645846856703)
                      ·
                        rfl

theorem cell23_3197667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3197667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197667 prefixEnd_3197667 := by exact prefixLift 3197667
  have htrace : WordTrace (prefixWord ++ tailWord_3197667) baseStart_3197667 baseEnd_3197667 := by
    simpa [prefixWord, tailWord_3197667, baseEnd_3197667] using wordTrace_append hprefix tailTrace_3197667
  have hstable : (prefixWord ++ tailWord_3197667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197667).length < 2 ^ (prefixWord ++ tailWord_3197667).sum := by decide
  have hdescent : baseEnd_3197667 < baseStart_3197667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197672 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3197672 : Nat := 118140960795 + 3197672 * 2 ^ 59
def prefixEnd_3197672 : Nat := 4983230072969 + 3 ^ 40 * 3197672 * 2
def baseEnd_3197672 : Nat := 1641942711423918327294181

theorem tailTrace_3197672 : CollatzResearch.WordTrace tailWord_3197672 prefixEnd_3197672 1641942711423918327294181 := by
  unfold tailWord_3197672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58314339635693968871981635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77752452847591958495975513 58314339635693968871981635)
  ·
    refine ⟨87471509453540953307972453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58314339635693968871981635 87471509453540953307972453)
    ·
      refine ⟨16400908022538928745244835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87471509453540953307972453 16400908022538928745244835)
      ·
        refine ⟨24601362033808393117867253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16400908022538928745244835 24601362033808393117867253)
        ·
          refine ⟨2306377690669536854800055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24601362033808393117867253 2306377690669536854800055)
          ·
            refine ⟨3459566536004305282200083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306377690669536854800055 3459566536004305282200083)
            ·
              refine ⟨5189349804006457923300125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459566536004305282200083 5189349804006457923300125)
              ·
                refine ⟨1946006176502421721237547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5189349804006457923300125 1946006176502421721237547)
                ·
                  refine ⟨2919009264753632581856321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946006176502421721237547 2919009264753632581856321)
                  ·
                    refine ⟨2189256948565224436392241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919009264753632581856321 2189256948565224436392241)
                    ·
                      refine ⟨1641942711423918327294181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189256948565224436392241 1641942711423918327294181)
                      ·
                        rfl

theorem cell23_3197672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3197672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197672 prefixEnd_3197672 := by exact prefixLift 3197672
  have htrace : WordTrace (prefixWord ++ tailWord_3197672) baseStart_3197672 baseEnd_3197672 := by
    simpa [prefixWord, tailWord_3197672, baseEnd_3197672] using wordTrace_append hprefix tailTrace_3197672
  have hstable : (prefixWord ++ tailWord_3197672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197672).length < 2 ^ (prefixWord ++ tailWord_3197672).sum := by decide
  have hdescent : baseEnd_3197672 < baseStart_3197672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197697 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3197697 : Nat := 118140960795 + 3197697 * 2 ^ 59
def prefixEnd_3197697 : Nat := 4983230072969 + 3 ^ 40 * 3197697 * 2
def baseEnd_3197697 : Nat := 1641955548440280729481565

theorem tailTrace_3197697 : CollatzResearch.WordTrace tailWord_3197697 prefixEnd_3197697 1641955548440280729481565 := by
  unfold tailWord_3197697
  simp only [CollatzResearch.WordTrace]
  refine ⟨116629591096297367013623345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77753060730864911342415563 116629591096297367013623345)
  ·
    refine ⟨87472193322223025260217509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116629591096297367013623345 87472193322223025260217509)
    ·
      refine ⟨16401036247916817236290783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87472193322223025260217509 16401036247916817236290783)
      ·
        refine ⟨24601554371875225854436175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16401036247916817236290783 24601554371875225854436175)
        ·
          refine ⟨36902331557812838781654263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24601554371875225854436175 36902331557812838781654263)
          ·
            refine ⟨55353497336719258172481395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36902331557812838781654263 55353497336719258172481395)
            ·
              refine ⟨83030246005078887258722093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55353497336719258172481395 83030246005078887258722093)
              ·
                refine ⟨31136342251904582722020785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83030246005078887258722093 31136342251904582722020785)
                ·
                  refine ⟨23352256688928437041515589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31136342251904582722020785 23352256688928437041515589)
                  ·
                    refine ⟨4378548129174081945284173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23352256688928437041515589 4378548129174081945284173)
                    ·
                      refine ⟨1641955548440280729481565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378548129174081945284173 1641955548440280729481565)
                      ·
                        rfl

theorem cell23_3197697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3197697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197697 prefixEnd_3197697 := by exact prefixLift 3197697
  have htrace : WordTrace (prefixWord ++ tailWord_3197697) baseStart_3197697 baseEnd_3197697 := by
    simpa [prefixWord, tailWord_3197697, baseEnd_3197697] using wordTrace_append hprefix tailTrace_3197697
  have hstable : (prefixWord ++ tailWord_3197697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197697).length < 2 ^ (prefixWord ++ tailWord_3197697).sum := by decide
  have hdescent : baseEnd_3197697 < baseStart_3197697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197711 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 2, 2, 2]
def baseStart_3197711 : Nat := 118140960795 + 3197711 * 2 ^ 59
def prefixEnd_3197711 : Nat := 4983230072969 + 3 ^ 40 * 3197711 * 2
def baseEnd_3197711 : Nat := 1641962737169443674706501

theorem tailTrace_3197711 : CollatzResearch.WordTrace tailWord_3197711 prefixEnd_3197711 1641962737169443674706501 := by
  unfold tailWord_3197711
  simp only [CollatzResearch.WordTrace]
  refine ⟨116630101718246647404632987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77753401145497764936421991 116630101718246647404632987)
  ·
    refine ⟨174945152577369971106949481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116630101718246647404632987 174945152577369971106949481)
    ·
      refine ⟨131208864433027478330212111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174945152577369971106949481 131208864433027478330212111)
      ·
        refine ⟨196813296649541217495318167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131208864433027478330212111 196813296649541217495318167)
        ·
          refine ⟨295219944974311826242977251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196813296649541217495318167 295219944974311826242977251)
          ·
            refine ⟨442829917461467739364465877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295219944974311826242977251 442829917461467739364465877)
            ·
              refine ⟨10378826190503150141354669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 442829917461467739364465877 10378826190503150141354669)
              ·
                refine ⟨3892059821438681303008001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10378826190503150141354669 3892059821438681303008001)
                ·
                  refine ⟨2919044866079010977256001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892059821438681303008001 2919044866079010977256001)
                  ·
                    refine ⟨2189283649559258232942001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919044866079010977256001 2189283649559258232942001)
                    ·
                      refine ⟨1641962737169443674706501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189283649559258232942001 1641962737169443674706501)
                      ·
                        rfl

theorem cell23_3197711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2, 2].length) (baseStart_3197711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197711 prefixEnd_3197711 := by exact prefixLift 3197711
  have htrace : WordTrace (prefixWord ++ tailWord_3197711) baseStart_3197711 baseEnd_3197711 := by
    simpa [prefixWord, tailWord_3197711, baseEnd_3197711] using wordTrace_append hprefix tailTrace_3197711
  have hstable : (prefixWord ++ tailWord_3197711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197711).length < 2 ^ (prefixWord ++ tailWord_3197711).sum := by decide
  have hdescent : baseEnd_3197711 < baseStart_3197711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197767 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3197767 : Nat := 118140960795 + 3197767 * 2 ^ 59
def prefixEnd_3197767 : Nat := 4983230072969 + 3 ^ 40 * 3197767 * 2
def baseEnd_3197767 : Nat := 1641991492086095455606243

theorem tailTrace_3197767 : CollatzResearch.WordTrace tailWord_3197767 prefixEnd_3197767 1641991492086095455606243 := by
  unfold tailWord_3197767
  simp only [CollatzResearch.WordTrace]
  refine ⟨116632144206043768968671555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77754762804029179312447703 116632144206043768968671555)
  ·
    refine ⟨174948216309065653453007333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116632144206043768968671555 174948216309065653453007333)
    ·
      refine ⟨32802790557949810022438875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174948216309065653453007333 32802790557949810022438875)
      ·
        refine ⟨49204185836924715033658313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32802790557949810022438875 49204185836924715033658313)
        ·
          refine ⟨36903139377693536275243735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49204185836924715033658313 36903139377693536275243735)
          ·
            refine ⟨55354709066540304412865603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36903139377693536275243735 55354709066540304412865603)
            ·
              refine ⟨83032063599810456619298405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55354709066540304412865603 83032063599810456619298405)
              ·
                refine ⟨15568511924964460616118451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83032063599810456619298405 15568511924964460616118451)
                ·
                  refine ⟨23352767887446690924177677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15568511924964460616118451 23352767887446690924177677)
                  ·
                    refine ⟨8757287957792509096566629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23352767887446690924177677 8757287957792509096566629)
                    ·
                      refine ⟨1641991492086095455606243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8757287957792509096566629 1641991492086095455606243)
                      ·
                        rfl

theorem cell23_3197767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3197767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197767 prefixEnd_3197767 := by exact prefixLift 3197767
  have htrace : WordTrace (prefixWord ++ tailWord_3197767) baseStart_3197767 baseEnd_3197767 := by
    simpa [prefixWord, tailWord_3197767, baseEnd_3197767] using wordTrace_append hprefix tailTrace_3197767
  have hstable : (prefixWord ++ tailWord_3197767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197767).length < 2 ^ (prefixWord ++ tailWord_3197767).sum := by decide
  have hdescent : baseEnd_3197767 < baseStart_3197767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197797 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3197797 : Nat := 118140960795 + 3197797 * 2 ^ 59
def prefixEnd_3197797 : Nat := 4983230072969 + 3 ^ 40 * 3197797 * 2
def baseEnd_3197797 : Nat := 1642006896505730338231105

theorem tailTrace_3197797 : CollatzResearch.WordTrace tailWord_3197797 prefixEnd_3197797 1642006896505730338231105 := by
  unfold tailWord_3197797
  simp only [CollatzResearch.WordTrace]
  refine ⟨116633238395935084092263645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77755492263956722728175763 116633238395935084092263645)
  ·
    refine ⟨43737464398475656534598867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116633238395935084092263645 43737464398475656534598867)
    ·
      refine ⟨65606196597713484801898301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43737464398475656534598867 65606196597713484801898301)
      ·
        refine ⟨24602323724142556800711863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65606196597713484801898301 24602323724142556800711863)
        ·
          refine ⟨36903485586213835201067795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602323724142556800711863 36903485586213835201067795)
          ·
            refine ⟨55355228379320752801601693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36903485586213835201067795 55355228379320752801601693)
            ·
              refine ⟨20758210642245282300600635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55355228379320752801601693 20758210642245282300600635)
              ·
                refine ⟨31137315963367923450900953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758210642245282300600635 31137315963367923450900953)
                ·
                  refine ⟨23352986972525942588175715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31137315963367923450900953 23352986972525942588175715)
                  ·
                    refine ⟨35029480458788913882263573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23352986972525942588175715 35029480458788913882263573)
                    ·
                      refine ⟨1642006896505730338231105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35029480458788913882263573 1642006896505730338231105)
                      ·
                        rfl

theorem cell23_3197797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3197797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197797 prefixEnd_3197797 := by exact prefixLift 3197797
  have htrace : WordTrace (prefixWord ++ tailWord_3197797) baseStart_3197797 baseEnd_3197797 := by
    simpa [prefixWord, tailWord_3197797, baseEnd_3197797] using wordTrace_append hprefix tailTrace_3197797
  have hstable : (prefixWord ++ tailWord_3197797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197797).length < 2 ^ (prefixWord ++ tailWord_3197797).sum := by decide
  have hdescent : baseEnd_3197797 < baseStart_3197797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197804 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_3197804 : Nat := 118140960795 + 3197804 * 2 ^ 59
def prefixEnd_3197804 : Nat := 4983230072969 + 3 ^ 40 * 3197804 * 2
def baseEnd_3197804 : Nat := 1642010490870311810843573

theorem tailTrace_3197804 : CollatzResearch.WordTrace tailWord_3197804 prefixEnd_3197804 1642010490870311810843573 := by
  unfold tailWord_3197804
  simp only [CollatzResearch.WordTrace]
  refine ⟨58316746853454862143884233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77755662471273149525178977 58316746853454862143884233)
  ·
    refine ⟨43737560140091146607913175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58316746853454862143884233 43737560140091146607913175)
    ·
      refine ⟨65606340210136719911869763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43737560140091146607913175 65606340210136719911869763)
      ·
        refine ⟨98409510315205079867804645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65606340210136719911869763 98409510315205079867804645)
        ·
          refine ⟨18451783184100952475213371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98409510315205079867804645 18451783184100952475213371)
          ·
            refine ⟨27677674776151428712820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18451783184100952475213371 27677674776151428712820057)
            ·
              refine ⟨20758256082113571534615043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27677674776151428712820057 20758256082113571534615043)
              ·
                refine ⟨31137384123170357301922565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758256082113571534615043 31137384123170357301922565)
                ·
                  refine ⟨5838259523094441994110481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31137384123170357301922565 5838259523094441994110481)
                  ·
                    refine ⟨4378694642320831495582861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5838259523094441994110481 4378694642320831495582861)
                    ·
                      refine ⟨1642010490870311810843573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378694642320831495582861 1642010490870311810843573)
                      ·
                        rfl

theorem cell23_3197804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_3197804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197804 prefixEnd_3197804 := by exact prefixLift 3197804
  have htrace : WordTrace (prefixWord ++ tailWord_3197804) baseStart_3197804 baseEnd_3197804 := by
    simpa [prefixWord, tailWord_3197804, baseEnd_3197804] using wordTrace_append hprefix tailTrace_3197804
  have hstable : (prefixWord ++ tailWord_3197804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197804).length < 2 ^ (prefixWord ++ tailWord_3197804).sum := by decide
  have hdescent : baseEnd_3197804 < baseStart_3197804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197811 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 1, 4]
def baseStart_3197811 : Nat := 118140960795 + 3197811 * 2 ^ 59
def prefixEnd_3197811 : Nat := 4983230072969 + 3 ^ 40 * 3197811 * 2
def baseEnd_3197811 : Nat := 547338028411631094485347

theorem tailTrace_3197811 : CollatzResearch.WordTrace tailWord_3197811 prefixEnd_3197811 547338028411631094485347 := by
  unfold tailWord_3197811
  simp only [CollatzResearch.WordTrace]
  refine ⟨116633749017884364483273287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77755832678589576322182191 116633749017884364483273287)
  ·
    refine ⟨174950623526826546724909931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116633749017884364483273287 174950623526826546724909931)
    ·
      refine ⟨262425935290239820087364897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174950623526826546724909931 262425935290239820087364897)
      ·
        refine ⟨196819451467679865065523673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262425935290239820087364897 196819451467679865065523673)
        ·
          refine ⟨147614588600759898799142755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196819451467679865065523673 147614588600759898799142755)
          ·
            refine ⟨221421882901139848198714133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147614588600759898799142755 221421882901139848198714133)
            ·
              refine ⟨10379150760990930384314725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221421882901139848198714133 10379150760990930384314725)
              ·
                refine ⟨1946090767685799447059011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10379150760990930384314725 1946090767685799447059011)
                ·
                  refine ⟨2919136151528699170588517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946090767685799447059011 2919136151528699170588517)
                  ·
                    refine ⟨547338028411631094485347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919136151528699170588517 547338028411631094485347)
                    ·
                      rfl

theorem cell23_3197811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 4].length) (baseStart_3197811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197811 prefixEnd_3197811 := by exact prefixLift 3197811
  have htrace : WordTrace (prefixWord ++ tailWord_3197811) baseStart_3197811 baseEnd_3197811 := by
    simpa [prefixWord, tailWord_3197811, baseEnd_3197811] using wordTrace_append hprefix tailTrace_3197811
  have hstable : (prefixWord ++ tailWord_3197811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197811).length < 2 ^ (prefixWord ++ tailWord_3197811).sum := by decide
  have hdescent : baseEnd_3197811 < baseStart_3197811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197827 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_3197827 : Nat := 118140960795 + 3197827 * 2 ^ 59
def prefixEnd_3197827 : Nat := 4983230072969 + 3 ^ 40 * 3197827 * 2
def baseEnd_3197827 : Nat := 1642022300925365220855967

theorem tailTrace_3197827 : CollatzResearch.WordTrace tailWord_3197827 prefixEnd_3197827 1642022300925365220855967 := by
  unfold tailWord_3197827
  simp only [CollatzResearch.WordTrace]
  refine ⟨116634332585826399215855735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77756221723884266143903823 116634332585826399215855735)
  ·
    refine ⟨174951498878739598823783603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116634332585826399215855735 174951498878739598823783603)
    ·
      refine ⟨262427248318109398235675405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174951498878739598823783603 262427248318109398235675405)
      ·
        refine ⟨98410218119291024338378277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262427248318109398235675405 98410218119291024338378277)
        ·
          refine ⟨18451915897367067063445927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98410218119291024338378277 18451915897367067063445927)
          ·
            refine ⟨27677873846050600595168891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18451915897367067063445927 27677873846050600595168891)
            ·
              refine ⟨41516810769075900892753337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27677873846050600595168891 41516810769075900892753337)
              ·
                refine ⟨31137608076806925669565003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41516810769075900892753337 31137608076806925669565003)
                ·
                  refine ⟨46706412115210388504347505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31137608076806925669565003 46706412115210388504347505)
                  ·
                    refine ⟨35029809086407791378260629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46706412115210388504347505 35029809086407791378260629)
                    ·
                      refine ⟨1642022300925365220855967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35029809086407791378260629 1642022300925365220855967)
                      ·
                        rfl

theorem cell23_3197827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_3197827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197827 prefixEnd_3197827 := by exact prefixLift 3197827
  have htrace : WordTrace (prefixWord ++ tailWord_3197827) baseStart_3197827 baseEnd_3197827 := by
    simpa [prefixWord, tailWord_3197827, baseEnd_3197827] using wordTrace_append hprefix tailTrace_3197827
  have hstable : (prefixWord ++ tailWord_3197827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197827).length < 2 ^ (prefixWord ++ tailWord_3197827).sum := by decide
  have hdescent : baseEnd_3197827 < baseStart_3197827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 6]
def baseStart_3197867 : Nat := 118140960795 + 3197867 * 2 ^ 59
def prefixEnd_3197867 : Nat := 4983230072969 + 3 ^ 40 * 3197867 * 2
def baseEnd_3197867 : Nat := 547347613383848354785261

theorem tailTrace_3197867 : CollatzResearch.WordTrace tailWord_3197867 prefixEnd_3197867 547347613383848354785261 := by
  unfold tailWord_3197867
  simp only [CollatzResearch.WordTrace]
  refine ⟨116635791505681486047311855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77757194337120990698207903 116635791505681486047311855)
  ·
    refine ⟨174953687258522229070967783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116635791505681486047311855 174953687258522229070967783)
    ·
      refine ⟨262430530887783343606451675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174953687258522229070967783 262430530887783343606451675)
      ·
        refine ⟨393645796331675015409677513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262430530887783343606451675 393645796331675015409677513)
        ·
          refine ⟨295234347248756261557258135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393645796331675015409677513 295234347248756261557258135)
          ·
            refine ⟨442851520873134392335887203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295234347248756261557258135 442851520873134392335887203)
            ·
              refine ⟨664277281309701588503830805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442851520873134392335887203 664277281309701588503830805)
              ·
                refine ⟨31137997561392261961117069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664277281309701588503830805 31137997561392261961117069)
                ·
                  refine ⟨11676749085522098235418901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31137997561392261961117069 11676749085522098235418901)
                  ·
                    refine ⟨547347613383848354785261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11676749085522098235418901 547347613383848354785261)
                    ·
                      rfl

theorem cell23_3197867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_3197867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197867 prefixEnd_3197867 := by exact prefixLift 3197867
  have htrace : WordTrace (prefixWord ++ tailWord_3197867) baseStart_3197867 baseEnd_3197867 := by
    simpa [prefixWord, tailWord_3197867, baseEnd_3197867] using wordTrace_append hprefix tailTrace_3197867
  have hstable : (prefixWord ++ tailWord_3197867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197867).length < 2 ^ (prefixWord ++ tailWord_3197867).sum := by decide
  have hdescent : baseEnd_3197867 < baseStart_3197867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197919 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 1, 1, 3]
def baseStart_3197919 : Nat := 118140960795 + 3197919 * 2 ^ 59
def prefixEnd_3197919 : Nat := 4983230072969 + 3 ^ 40 * 3197919 * 2
def baseEnd_3197919 : Nat := 1642069541145578860905545

theorem tailTrace_3197919 : CollatzResearch.WordTrace tailWord_3197919 prefixEnd_3197919 1642069541145578860905545 := by
  unfold tailWord_3197919
  simp only [CollatzResearch.WordTrace]
  refine ⟨116637688101493098928204811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77758458734328732618803207 116637688101493098928204811)
  ·
    refine ⟨174956532152239648392307217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116637688101493098928204811 174956532152239648392307217)
    ·
      refine ⟨131217399114179736294230413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174956532152239648392307217 131217399114179736294230413)
      ·
        refine ⟨49206524667817401110336405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131217399114179736294230413 49206524667817401110336405)
        ·
          refine ⟨2306555843803940677047019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49206524667817401110336405 2306555843803940677047019)
          ·
            refine ⟨3459833765705911015570529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306555843803940677047019 3459833765705911015570529)
            ·
              refine ⟨2594875324279433261677897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459833765705911015570529 2594875324279433261677897)
              ·
                refine ⟨1946156493209574946258423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594875324279433261677897 1946156493209574946258423)
                ·
                  refine ⟨2919234739814362419387635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946156493209574946258423 2919234739814362419387635)
                  ·
                    refine ⟨4378852109721543629081453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919234739814362419387635 4378852109721543629081453)
                    ·
                      refine ⟨1642069541145578860905545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378852109721543629081453 1642069541145578860905545)
                      ·
                        rfl

theorem cell23_3197919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_3197919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197919 prefixEnd_3197919 := by exact prefixLift 3197919
  have htrace : WordTrace (prefixWord ++ tailWord_3197919) baseStart_3197919 baseEnd_3197919 := by
    simpa [prefixWord, tailWord_3197919, baseEnd_3197919] using wordTrace_append hprefix tailTrace_3197919
  have hstable : (prefixWord ++ tailWord_3197919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197919).length < 2 ^ (prefixWord ++ tailWord_3197919).sum := by decide
  have hdescent : baseEnd_3197919 < baseStart_3197919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197975 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3197975 : Nat := 118140960795 + 3197975 * 2 ^ 59
def prefixEnd_3197975 : Nat := 4983230072969 + 3 ^ 40 * 3197975 * 2
def baseEnd_3197975 : Nat := 1642098296062230641805287

theorem tailTrace_3197975 : CollatzResearch.WordTrace tailWord_3197975 prefixEnd_3197975 1642098296062230641805287 := by
  unfold tailWord_3197975
  simp only [CollatzResearch.WordTrace]
  refine ⟨116639730589290220492243379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77759820392860146994828919 116639730589290220492243379)
  ·
    refine ⟨174959595883935330738365069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116639730589290220492243379 174959595883935330738365069)
    ·
      refine ⟨65609848456475749026886901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174959595883935330738365069 65609848456475749026886901)
      ·
        refine ⟨6150923292794601471270647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65609848456475749026886901 6150923292794601471270647)
        ·
          refine ⟨9226384939191902206905971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150923292794601471270647 9226384939191902206905971)
          ·
            refine ⟨13839577408787853310358957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226384939191902206905971 13839577408787853310358957)
            ·
              refine ⟨5189841528295444991384609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13839577408787853310358957 5189841528295444991384609)
              ·
                refine ⟨3892381146221583743538457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189841528295444991384609 3892381146221583743538457)
                ·
                  refine ⟨2919285859666187807653843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892381146221583743538457 2919285859666187807653843)
                  ·
                    refine ⟨4378928789499281711480765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919285859666187807653843 4378928789499281711480765)
                    ·
                      refine ⟨1642098296062230641805287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4378928789499281711480765 1642098296062230641805287)
                      ·
                        rfl

theorem cell23_3197975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3197975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197975 prefixEnd_3197975 := by exact prefixLift 3197975
  have htrace : WordTrace (prefixWord ++ tailWord_3197975) baseStart_3197975 baseEnd_3197975 := by
    simpa [prefixWord, tailWord_3197975, baseEnd_3197975] using wordTrace_append hprefix tailTrace_3197975
  have hstable : (prefixWord ++ tailWord_3197975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197975).length < 2 ^ (prefixWord ++ tailWord_3197975).sum := by decide
  have hdescent : baseEnd_3197975 < baseStart_3197975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198074 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3198074 : Nat := 118140960795 + 3198074 * 2 ^ 59
def prefixEnd_3198074 : Nat := 4983230072969 + 3 ^ 40 * 3198074 * 2
def baseEnd_3198074 : Nat := 1642149130647025754467331

theorem tailTrace_3198074 : CollatzResearch.WordTrace tailWord_3198074 prefixEnd_3198074 1642149130647025754467331 := by
  unfold tailWord_3198074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160835353982890100024319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77762227610621040266731517 29160835353982890100024319)
  ·
    refine ⟨43741253030974335150036479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29160835353982890100024319 43741253030974335150036479)
    ·
      refine ⟨65611879546461502725054719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43741253030974335150036479 65611879546461502725054719)
      ·
        refine ⟨98417819319692254087582079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65611879546461502725054719 98417819319692254087582079)
        ·
          refine ⟨147626728979538381131373119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98417819319692254087582079 147626728979538381131373119)
          ·
            refine ⟨221440093469307571697059679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147626728979538381131373119 221440093469307571697059679)
            ·
              refine ⟨332160140203961357545589519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221440093469307571697059679 332160140203961357545589519)
              ·
                refine ⟨498240210305942036318384279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332160140203961357545589519 498240210305942036318384279)
                ·
                  refine ⟨747360315458913054477576419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498240210305942036318384279 747360315458913054477576419)
                  ·
                    refine ⟨1121040473188369581716364629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747360315458913054477576419 1121040473188369581716364629)
                    ·
                      refine ⟨1642149130647025754467331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1121040473188369581716364629 1642149130647025754467331)
                      ·
                        rfl

theorem cell23_3198074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3198074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198074 prefixEnd_3198074 := by exact prefixLift 3198074
  have htrace : WordTrace (prefixWord ++ tailWord_3198074) baseStart_3198074 baseEnd_3198074 := by
    simpa [prefixWord, tailWord_3198074, baseEnd_3198074] using wordTrace_append hprefix tailTrace_3198074
  have hstable : (prefixWord ++ tailWord_3198074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198074).length < 2 ^ (prefixWord ++ tailWord_3198074).sum := by decide
  have hdescent : baseEnd_3198074 < baseStart_3198074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198122 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3198122 : Nat := 118140960795 + 3198122 * 2 ^ 59
def prefixEnd_3198122 : Nat := 4983230072969 + 3 ^ 40 * 3198122 * 2
def baseEnd_3198122 : Nat := 1642173777718441566667111

theorem tailTrace_3198122 : CollatzResearch.WordTrace tailWord_3198122 prefixEnd_3198122 1642173777718441566667111 := by
  unfold tailWord_3198122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161273029939416149461155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77763394746505109731896413 29161273029939416149461155)
  ·
    refine ⟨43741909544909124224191733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29161273029939416149461155 43741909544909124224191733)
    ·
      refine ⟨4100804019835230396017975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43741909544909124224191733 4100804019835230396017975)
      ·
        refine ⟨6151206029752845594026963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100804019835230396017975 6151206029752845594026963)
        ·
          refine ⟨9226809044629268391040445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151206029752845594026963 9226809044629268391040445)
          ·
            refine ⟨3460053391735975646640167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9226809044629268391040445 3460053391735975646640167)
            ·
              refine ⟨5190080087603963469960251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460053391735975646640167 5190080087603963469960251)
              ·
                refine ⟨7785120131405945204940377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190080087603963469960251 7785120131405945204940377)
                ·
                  refine ⟨5838840098554458903705283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785120131405945204940377 5838840098554458903705283)
                  ·
                    refine ⟨8758260147831688355557925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838840098554458903705283 8758260147831688355557925)
                    ·
                      refine ⟨1642173777718441566667111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8758260147831688355557925 1642173777718441566667111)
                      ·
                        rfl

theorem cell23_3198122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3198122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198122 prefixEnd_3198122 := by exact prefixLift 3198122
  have htrace : WordTrace (prefixWord ++ tailWord_3198122) baseStart_3198122 baseEnd_3198122 := by
    simpa [prefixWord, tailWord_3198122, baseEnd_3198122] using wordTrace_append hprefix tailTrace_3198122
  have hstable : (prefixWord ++ tailWord_3198122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198122).length < 2 ^ (prefixWord ++ tailWord_3198122).sum := by decide
  have hdescent : baseEnd_3198122 < baseStart_3198122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198125 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3198125 : Nat := 118140960795 + 3198125 * 2 ^ 59
def prefixEnd_3198125 : Nat := 4983230072969 + 3 ^ 40 * 3198125 * 2
def baseEnd_3198125 : Nat := 1642175318160405054929597

theorem tailTrace_3198125 : CollatzResearch.WordTrace tailWord_3198125 prefixEnd_3198125 1642175318160405054929597 := by
  unfold tailWord_3198125
  simp only [CollatzResearch.WordTrace]
  refine ⟨116645201538746796110203829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77763467692497864073469219 116645201538746796110203829)
  ·
    refine ⟨10935487644257512135331609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116645201538746796110203829 10935487644257512135331609)
    ·
      refine ⟨8201615733193134101498707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10935487644257512135331609 8201615733193134101498707)
      ·
        refine ⟨12302423599789701152248061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201615733193134101498707 12302423599789701152248061)
        ·
          refine ⟨4613408849921137932093023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12302423599789701152248061 4613408849921137932093023)
          ·
            refine ⟨6920113274881706898139535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613408849921137932093023 6920113274881706898139535)
            ·
              refine ⟨10380169912322560347209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920113274881706898139535 10380169912322560347209303)
              ·
                refine ⟨15570254868483840520813955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380169912322560347209303 15570254868483840520813955)
                ·
                  refine ⟨23355382302725760781220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15570254868483840520813955 23355382302725760781220933)
                  ·
                    refine ⟨4379134181761080146478925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23355382302725760781220933 4379134181761080146478925)
                    ·
                      refine ⟨1642175318160405054929597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379134181761080146478925 1642175318160405054929597)
                      ·
                        rfl

theorem cell23_3198125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3198125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198125 prefixEnd_3198125 := by exact prefixLift 3198125
  have htrace : WordTrace (prefixWord ++ tailWord_3198125) baseStart_3198125 baseEnd_3198125 := by
    simpa [prefixWord, tailWord_3198125, baseEnd_3198125] using wordTrace_append hprefix tailTrace_3198125
  have hstable : (prefixWord ++ tailWord_3198125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198125).length < 2 ^ (prefixWord ++ tailWord_3198125).sum := by decide
  have hdescent : baseEnd_3198125 < baseStart_3198125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198138 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_3198138 : Nat := 118140960795 + 3198138 * 2 ^ 59
def prefixEnd_3198138 : Nat := 4983230072969 + 3 ^ 40 * 3198138 * 2
def baseEnd_3198138 : Nat := 1642181993408913504067037

theorem tailTrace_3198138 : CollatzResearch.WordTrace tailWord_3198138 prefixEnd_3198138 1642181993408913504067037 := by
  unfold tailWord_3198138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161418921924924832606767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77763783791799799553618045 29161418921924924832606767)
  ·
    refine ⟨43742128382887387248910151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29161418921924924832606767 43742128382887387248910151)
    ·
      refine ⟨65613192574331080873365227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43742128382887387248910151 65613192574331080873365227)
      ·
        refine ⟨98419788861496621310047841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65613192574331080873365227 98419788861496621310047841)
        ·
          refine ⟨73814841646122465982535881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98419788861496621310047841 73814841646122465982535881)
          ·
            refine ⟨55361131234591849486901911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73814841646122465982535881 55361131234591849486901911)
            ·
              refine ⟨83041696851887774230352867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55361131234591849486901911 83041696851887774230352867)
              ·
                refine ⟨124562545277831661345529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83041696851887774230352867 124562545277831661345529301)
                ·
                  refine ⟨2919434654949179562785843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 124562545277831661345529301 2919434654949179562785843)
                  ·
                    refine ⟨4379151982423769344178765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919434654949179562785843 4379151982423769344178765)
                    ·
                      refine ⟨1642181993408913504067037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379151982423769344178765 1642181993408913504067037)
                      ·
                        rfl

theorem cell23_3198138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_3198138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198138 prefixEnd_3198138 := by exact prefixLift 3198138
  have htrace : WordTrace (prefixWord ++ tailWord_3198138) baseStart_3198138 baseEnd_3198138 := by
    simpa [prefixWord, tailWord_3198138, baseEnd_3198138] using wordTrace_append hprefix tailTrace_3198138
  have hstable : (prefixWord ++ tailWord_3198138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198138).length < 2 ^ (prefixWord ++ tailWord_3198138).sum := by decide
  have hdescent : baseEnd_3198138 < baseStart_3198138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198145 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 6]
def baseStart_3198145 : Nat := 118140960795 + 3198145 * 2 ^ 59
def prefixEnd_3198145 : Nat := 4983230072969 + 3 ^ 40 * 3198145 * 2
def baseEnd_3198145 : Nat := 182465065308166108519945

theorem tailTrace_3198145 : CollatzResearch.WordTrace tailWord_3198145 prefixEnd_3198145 182465065308166108519945 := by
  unfold tailWord_3198145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116645930998674339525931889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77763953999116226350621259 116645930998674339525931889)
  ·
    refine ⟨87484448249005754644448917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116645930998674339525931889 87484448249005754644448917)
    ·
      refine ⟨4100833511672144748958543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87484448249005754644448917 4100833511672144748958543)
      ·
        refine ⟨6151250267508217123437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100833511672144748958543 6151250267508217123437815)
        ·
          refine ⟨9226875401262325685156723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151250267508217123437815 9226875401262325685156723)
          ·
            refine ⟨13840313101893488527735085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226875401262325685156723 13840313101893488527735085)
            ·
              refine ⟨5190117413210058197900657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13840313101893488527735085 5190117413210058197900657)
              ·
                refine ⟨3892588059907543648425493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190117413210058197900657 3892588059907543648425493)
                ·
                  refine ⟨182465065308166108519945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3892588059907543648425493 182465065308166108519945)
                  ·
                    rfl

theorem cell23_3198145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_3198145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198145 prefixEnd_3198145 := by exact prefixLift 3198145
  have htrace : WordTrace (prefixWord ++ tailWord_3198145) baseStart_3198145 baseEnd_3198145 := by
    simpa [prefixWord, tailWord_3198145, baseEnd_3198145] using wordTrace_append hprefix tailTrace_3198145
  have hstable : (prefixWord ++ tailWord_3198145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198145).length < 2 ^ (prefixWord ++ tailWord_3198145).sum := by decide
  have hdescent : baseEnd_3198145 < baseStart_3198145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198165 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3198165 : Nat := 118140960795 + 3198165 * 2 ^ 59
def prefixEnd_3198165 : Nat := 4983230072969 + 3 ^ 40 * 3198165 * 2
def baseEnd_3198165 : Nat := 1642195857386584898429413

theorem tailTrace_3198165 : CollatzResearch.WordTrace tailWord_3198165 prefixEnd_3198165 1642195857386584898429413 := by
  unfold tailWord_3198165
  simp only [CollatzResearch.WordTrace]
  refine ⟨116646660458601882941659949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77764440305734588627773299 116646660458601882941659949)
  ·
    refine ⟨43742497671975706103122481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116646660458601882941659949 43742497671975706103122481)
    ·
      refine ⟨32806873253981779577341861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43742497671975706103122481 32806873253981779577341861)
      ·
        refine ⟨6151288735121583670751599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32806873253981779577341861 6151288735121583670751599)
        ·
          refine ⟨9226933102682375506127399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151288735121583670751599 9226933102682375506127399)
          ·
            refine ⟨13840399654023563259191099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226933102682375506127399 13840399654023563259191099)
            ·
              refine ⟨20760599481035344888786649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13840399654023563259191099 20760599481035344888786649)
              ·
                refine ⟨15570449610776508666589987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20760599481035344888786649 15570449610776508666589987)
                ·
                  refine ⟨23355674416164762999884981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15570449610776508666589987 23355674416164762999884981)
                  ·
                    refine ⟨2189594476515446531239217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23355674416164762999884981 2189594476515446531239217)
                    ·
                      refine ⟨1642195857386584898429413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189594476515446531239217 1642195857386584898429413)
                      ·
                        rfl

theorem cell23_3198165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3198165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198165 prefixEnd_3198165 := by exact prefixLift 3198165
  have htrace : WordTrace (prefixWord ++ tailWord_3198165) baseStart_3198165 baseEnd_3198165 := by
    simpa [prefixWord, tailWord_3198165, baseEnd_3198165] using wordTrace_append hprefix tailTrace_3198165
  have hstable : (prefixWord ++ tailWord_3198165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198165).length < 2 ^ (prefixWord ++ tailWord_3198165).sum := by decide
  have hdescent : baseEnd_3198165 < baseStart_3198165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198188 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_3198188 : Nat := 118140960795 + 3198188 * 2 ^ 59
def prefixEnd_3198188 : Nat := 4983230072969 + 3 ^ 40 * 3198188 * 2
def baseEnd_3198188 : Nat := 547402555813879436147269

theorem tailTrace_3198188 : CollatzResearch.WordTrace tailWord_3198188 prefixEnd_3198188 547402555813879436147269 := by
  unfold tailWord_3198188
  simp only [CollatzResearch.WordTrace]
  refine ⟨58323749668759278934873609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77764999558345705246498145 58323749668759278934873609)
  ·
    refine ⟨43742812251569459201155207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58323749668759278934873609 43742812251569459201155207)
    ·
      refine ⟨65614218377354188801732811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43742812251569459201155207 65614218377354188801732811)
      ·
        refine ⟨98421327566031283202599217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65614218377354188801732811 98421327566031283202599217)
        ·
          refine ⟨73815995674523462401949413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98421327566031283202599217 73815995674523462401949413)
          ·
            refine ⟨13840499188973149200365515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73815995674523462401949413 13840499188973149200365515)
            ·
              refine ⟨20760748783459723800548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13840499188973149200365515 20760748783459723800548273)
              ·
                refine ⟨15570561587594792850411205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20760748783459723800548273 15570561587594792850411205)
                ·
                  refine ⟨2919480297674023659452101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15570561587594792850411205 2919480297674023659452101)
                  ·
                    refine ⟨547402555813879436147269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919480297674023659452101 547402555813879436147269)
                    ·
                      rfl

theorem cell23_3198188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_3198188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198188 prefixEnd_3198188 := by exact prefixLift 3198188
  have htrace : WordTrace (prefixWord ++ tailWord_3198188) baseStart_3198188 baseEnd_3198188 := by
    simpa [prefixWord, tailWord_3198188, baseEnd_3198188] using wordTrace_append hprefix tailTrace_3198188
  have hstable : (prefixWord ++ tailWord_3198188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198188).length < 2 ^ (prefixWord ++ tailWord_3198188).sum := by decide
  have hdescent : baseEnd_3198188 < baseStart_3198188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198189 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3198189 : Nat := 118140960795 + 3198189 * 2 ^ 59
def prefixEnd_3198189 : Nat := 4983230072969 + 3 ^ 40 * 3198189 * 2
def baseEnd_3198189 : Nat := 1642208180922292804529303

theorem tailTrace_3198189 : CollatzResearch.WordTrace tailWord_3198189 prefixEnd_3198189 1642208180922292804529303 := by
  unfold tailWord_3198189
  simp only [CollatzResearch.WordTrace]
  refine ⟨116647535810514935040533621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77765023873676623360355747 116647535810514935040533621)
  ·
    refine ⟨10935706482235775160050027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116647535810514935040533621 10935706482235775160050027)
    ·
      refine ⟨16403559723353662740075041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10935706482235775160050027 16403559723353662740075041)
      ·
        refine ⟨12302669792515247055056281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16403559723353662740075041 12302669792515247055056281)
        ·
          refine ⟨9227002344386435291292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12302669792515247055056281 9227002344386435291292211)
          ·
            refine ⟨13840503516579652936938317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227002344386435291292211 13840503516579652936938317)
            ·
              refine ⟨5190188818717369851351869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13840503516579652936938317 5190188818717369851351869)
              ·
                refine ⟨1946320807019013694256951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5190188818717369851351869 1946320807019013694256951)
                ·
                  refine ⟨2919481210528520541385427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946320807019013694256951 2919481210528520541385427)
                  ·
                    refine ⟨4379221815792780812078141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919481210528520541385427 4379221815792780812078141)
                    ·
                      refine ⟨1642208180922292804529303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379221815792780812078141 1642208180922292804529303)
                      ·
                        rfl

theorem cell23_3198189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3198189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198189 prefixEnd_3198189 := by exact prefixLift 3198189
  have htrace : WordTrace (prefixWord ++ tailWord_3198189) baseStart_3198189 baseEnd_3198189 := by
    simpa [prefixWord, tailWord_3198189, baseEnd_3198189] using wordTrace_append hprefix tailTrace_3198189
  have hstable : (prefixWord ++ tailWord_3198189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198189).length < 2 ^ (prefixWord ++ tailWord_3198189).sum := by decide
  have hdescent : baseEnd_3198189 < baseStart_3198189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198206 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_3198206 : Nat := 118140960795 + 3198206 * 2 ^ 59
def prefixEnd_3198206 : Nat := 4983230072969 + 3 ^ 40 * 3198206 * 2
def baseEnd_3198206 : Nat := 1642216910093419238016725

theorem tailTrace_3198206 : CollatzResearch.WordTrace tailWord_3198206 prefixEnd_3198206 1642216910093419238016725 := by
  unfold tailWord_3198206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581019481431668367987809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77765437234302231295934981 14581019481431668367987809)
  ·
    refine ⟨10935764611073751275990857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581019481431668367987809 10935764611073751275990857)
    ·
      refine ⟨8201823458305313456993143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10935764611073751275990857 8201823458305313456993143)
      ·
        refine ⟨12302735187457970185489715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201823458305313456993143 12302735187457970185489715)
        ·
          refine ⟨18454102781186955278234573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12302735187457970185489715 18454102781186955278234573)
          ·
            refine ⟨6920288542945108229337965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18454102781186955278234573 6920288542945108229337965)
            ·
              refine ⟨2595108203604415586001737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6920288542945108229337965 2595108203604415586001737)
              ·
                refine ⟨1946331152703311689501303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595108203604415586001737 1946331152703311689501303)
                ·
                  refine ⟨2919496729054967534251955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946331152703311689501303 2919496729054967534251955)
                  ·
                    refine ⟨4379245093582451301377933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919496729054967534251955 4379245093582451301377933)
                    ·
                      refine ⟨1642216910093419238016725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379245093582451301377933 1642216910093419238016725)
                      ·
                        rfl

theorem cell23_3198206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_3198206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198206 prefixEnd_3198206 := by exact prefixLift 3198206
  have htrace : WordTrace (prefixWord ++ tailWord_3198206) baseStart_3198206 baseEnd_3198206 := by
    simpa [prefixWord, tailWord_3198206, baseEnd_3198206] using wordTrace_append hprefix tailTrace_3198206
  have hstable : (prefixWord ++ tailWord_3198206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198206).length < 2 ^ (prefixWord ++ tailWord_3198206).sum := by decide
  have hdescent : baseEnd_3198206 < baseStart_3198206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198222 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3198222 : Nat := 118140960795 + 3198222 * 2 ^ 59
def prefixEnd_3198222 : Nat := 4983230072969 + 3 ^ 40 * 3198222 * 2
def baseEnd_3198222 : Nat := 547408375261297058472217

theorem tailTrace_3198222 : CollatzResearch.WordTrace tailWord_3198222 prefixEnd_3198222 547408375261297058472217 := by
  unfold tailWord_3198222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581092427424422709560615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77765826279596921117656613 14581092427424422709560615)
  ·
    refine ⟨21871638641136634064340923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14581092427424422709560615 21871638641136634064340923)
    ·
      refine ⟨32807457961704951096511385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21871638641136634064340923 32807457961704951096511385)
      ·
        refine ⟨24605593471278713322383539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32807457961704951096511385 24605593471278713322383539)
        ·
          refine ⟨36908390206918069983575309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24605593471278713322383539 36908390206918069983575309)
          ·
            refine ⟨13840646327594276243840741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36908390206918069983575309 13840646327594276243840741)
            ·
              refine ⟨2595121186423926795720139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13840646327594276243840741 2595121186423926795720139)
              ·
                refine ⟨3892681779635890193580209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595121186423926795720139 3892681779635890193580209)
                ·
                  refine ⟨2919511334726917645185157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892681779635890193580209 2919511334726917645185157)
                  ·
                    refine ⟨547408375261297058472217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919511334726917645185157 547408375261297058472217)
                    ·
                      rfl

theorem cell23_3198222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3198222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198222 prefixEnd_3198222 := by exact prefixLift 3198222
  have htrace : WordTrace (prefixWord ++ tailWord_3198222) baseStart_3198222 baseEnd_3198222 := by
    simpa [prefixWord, tailWord_3198222, baseEnd_3198222] using wordTrace_append hprefix tailTrace_3198222
  have hstable : (prefixWord ++ tailWord_3198222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198222).length < 2 ^ (prefixWord ++ tailWord_3198222).sum := by decide
  have hdescent : baseEnd_3198222 < baseStart_3198222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198226 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3198226 : Nat := 118140960795 + 3198226 * 2 ^ 59
def prefixEnd_3198226 : Nat := 4983230072969 + 3 ^ 40 * 3198226 * 2
def baseEnd_3198226 : Nat := 547409059902169719922211

theorem tailTrace_3198226 : CollatzResearch.WordTrace tailWord_3198226 prefixEnd_3198226 547409059902169719922211 := by
  unfold tailWord_3198226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162221327845222589907633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77765923540920593573087021 29162221327845222589907633)
  ·
    refine ⟨21871665995883916942430725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29162221327845222589907633 21871665995883916942430725)
    ·
      refine ⟨4100937374228234426705761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21871665995883916942430725 4100937374228234426705761)
      ·
        refine ⟨3075703030671175820029321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100937374228234426705761 3075703030671175820029321)
        ·
          refine ⟨2306777273003381865021991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075703030671175820029321 2306777273003381865021991)
          ·
            refine ⟨3460165909505072797532987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306777273003381865021991 3460165909505072797532987)
            ·
              refine ⟨5190248864257609196299481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460165909505072797532987 5190248864257609196299481)
              ·
                refine ⟨3892686648193206897224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190248864257609196299481 3892686648193206897224611)
                ·
                  refine ⟨5839029972289810345836917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892686648193206897224611 5839029972289810345836917)
                  ·
                    refine ⟨547409059902169719922211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5839029972289810345836917 547409059902169719922211)
                    ·
                      rfl

theorem cell23_3198226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3198226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198226 prefixEnd_3198226 := by exact prefixLift 3198226
  have htrace : WordTrace (prefixWord ++ tailWord_3198226) baseStart_3198226 baseEnd_3198226 := by
    simpa [prefixWord, tailWord_3198226, baseEnd_3198226] using wordTrace_append hprefix tailTrace_3198226
  have hstable : (prefixWord ++ tailWord_3198226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198226).length < 2 ^ (prefixWord ++ tailWord_3198226).sum := by decide
  have hdescent : baseEnd_3198226 < baseStart_3198226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198232 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3198232 : Nat := 118140960795 + 3198232 * 2 ^ 59
def prefixEnd_3198232 : Nat := 4983230072969 + 3 ^ 40 * 3198232 * 2
def baseEnd_3198232 : Nat := 1642230260590436136291605

theorem tailTrace_3198232 : CollatzResearch.WordTrace tailWord_3198232 prefixEnd_3198232 1642230260590436136291605 := by
  unfold tailWord_3198232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58324552074679576692174475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77766069432906102256232633 58324552074679576692174475)
  ·
    refine ⟨87486828112019365038261713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58324552074679576692174475 87486828112019365038261713)
    ·
      refine ⟨65615121084014523778696285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87486828112019365038261713 65615121084014523778696285)
      ·
        refine ⟨24605670406505446417011107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65615121084014523778696285 24605670406505446417011107)
        ·
          refine ⟨36908505609758169625516661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24605670406505446417011107 36908505609758169625516661)
          ·
            refine ⟨3460172400914828402392187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36908505609758169625516661 3460172400914828402392187)
            ·
              refine ⟨5190258601372242603588281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460172400914828402392187 5190258601372242603588281)
              ·
                refine ⟨3892693951029181952691211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190258601372242603588281 3892693951029181952691211)
                ·
                  refine ⟨5839040926543772929036817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892693951029181952691211 5839040926543772929036817)
                  ·
                    refine ⟨4379280694907829696777613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839040926543772929036817 4379280694907829696777613)
                    ·
                      refine ⟨1642230260590436136291605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379280694907829696777613 1642230260590436136291605)
                      ·
                        rfl

theorem cell23_3198232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3198232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198232 prefixEnd_3198232 := by exact prefixLift 3198232
  have htrace : WordTrace (prefixWord ++ tailWord_3198232) baseStart_3198232 baseEnd_3198232 := by
    simpa [prefixWord, tailWord_3198232, baseEnd_3198232] using wordTrace_append hprefix tailTrace_3198232
  have hstable : (prefixWord ++ tailWord_3198232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198232).length < 2 ^ (prefixWord ++ tailWord_3198232).sum := by decide
  have hdescent : baseEnd_3198232 < baseStart_3198232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198245 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_3198245 : Nat := 118140960795 + 3198245 * 2 ^ 59
def prefixEnd_3198245 : Nat := 4983230072969 + 3 ^ 40 * 3198245 * 2
def baseEnd_3198245 : Nat := 1642236935838944585429045

theorem tailTrace_3198245 : CollatzResearch.WordTrace tailWord_3198245 prefixEnd_3198245 1642236935838944585429045 := by
  unfold tailWord_3198245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116649578298312056604572189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77766385532208037736381459 116649578298312056604572189)
  ·
    refine ⟨43743591861867021226714571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116649578298312056604572189 43743591861867021226714571)
    ·
      refine ⟨65615387792800531840071857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43743591861867021226714571 65615387792800531840071857)
      ·
        refine ⟨49211540844600398880053893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65615387792800531840071857 49211540844600398880053893)
        ·
          refine ⟨9227163908362574790010105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49211540844600398880053893 9227163908362574790010105)
          ·
            refine ⟨6920372931271931092507579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9227163908362574790010105 6920372931271931092507579)
            ·
              refine ⟨10380559396907896638761369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920372931271931092507579 10380559396907896638761369)
              ·
                refine ⟨7785419547680922479071027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10380559396907896638761369 7785419547680922479071027)
                ·
                  refine ⟨11678129321521383718606541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7785419547680922479071027 11678129321521383718606541)
                  ·
                    refine ⟨4379298495570518894477453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11678129321521383718606541 4379298495570518894477453)
                    ·
                      refine ⟨1642236935838944585429045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379298495570518894477453 1642236935838944585429045)
                      ·
                        rfl

theorem cell23_3198245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_3198245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198245 prefixEnd_3198245 := by exact prefixLift 3198245
  have htrace : WordTrace (prefixWord ++ tailWord_3198245) baseStart_3198245 baseEnd_3198245 := by
    simpa [prefixWord, tailWord_3198245, baseEnd_3198245] using wordTrace_append hprefix tailTrace_3198245
  have hstable : (prefixWord ++ tailWord_3198245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198245).length < 2 ^ (prefixWord ++ tailWord_3198245).sum := by decide
  have hdescent : baseEnd_3198245 < baseStart_3198245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198268 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3198268 : Nat := 118140960795 + 3198268 * 2 ^ 59
def prefixEnd_3198268 : Nat := 4983230072969 + 3 ^ 40 * 3198268 * 2
def baseEnd_3198268 : Nat := 1642248745893997995441439

theorem tailTrace_3198268 : CollatzResearch.WordTrace tailWord_3198268 prefixEnd_3198268 1642248745893997995441439 := by
  unfold tailWord_3198268
  simp only [CollatzResearch.WordTrace]
  refine ⟨58325208588614365766329729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77766944784819154355106305 58325208588614365766329729)
  ·
    refine ⟨43743906441460774324747297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58325208588614365766329729 43743906441460774324747297)
    ·
      refine ⟨32807929831095580743560473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43743906441460774324747297 32807929831095580743560473)
      ·
        refine ⟨24605947373321685557670355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32807929831095580743560473 24605947373321685557670355)
        ·
          refine ⟨36908921059982528336505533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24605947373321685557670355 36908921059982528336505533)
          ·
            refine ⟨13840845397493448126189575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36908921059982528336505533 13840845397493448126189575)
            ·
              refine ⟨20761268096240172189284363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13840845397493448126189575 20761268096240172189284363)
              ·
                refine ⟨31141902144360258283926545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20761268096240172189284363 31141902144360258283926545)
                ·
                  refine ⟨23356426608270193712944909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31141902144360258283926545 23356426608270193712944909)
                  ·
                    refine ⟨8758659978101322642354341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23356426608270193712944909 8758659978101322642354341)
                    ·
                      refine ⟨1642248745893997995441439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8758659978101322642354341 1642248745893997995441439)
                      ·
                        rfl

theorem cell23_3198268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3198268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198268 prefixEnd_3198268 := by exact prefixLift 3198268
  have htrace : WordTrace (prefixWord ++ tailWord_3198268) baseStart_3198268 baseEnd_3198268 := by
    simpa [prefixWord, tailWord_3198268, baseEnd_3198268] using wordTrace_append hprefix tailTrace_3198268
  have hstable : (prefixWord ++ tailWord_3198268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198268).length < 2 ^ (prefixWord ++ tailWord_3198268).sum := by decide
  have hdescent : baseEnd_3198268 < baseStart_3198268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198288 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_3198288 : Nat := 118140960795 + 3198288 * 2 ^ 59
def prefixEnd_3198288 : Nat := 4983230072969 + 3 ^ 40 * 3198288 * 2
def baseEnd_3198288 : Nat := 1642259015507087917191347

theorem tailTrace_3198288 : CollatzResearch.WordTrace tailWord_3198288 prefixEnd_3198288 1642259015507087917191347 := by
  unfold tailWord_3198288
  simp only [CollatzResearch.WordTrace]
  refine ⟨58325573318578137474193759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77767431091437516632258345 58325573318578137474193759)
  ·
    refine ⟨87488359977867206211290639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58325573318578137474193759 87488359977867206211290639)
    ·
      refine ⟨131232539966800809316935959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87488359977867206211290639 131232539966800809316935959)
      ·
        refine ⟨196848809950201213975403939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131232539966800809316935959 196848809950201213975403939)
        ·
          refine ⟨295273214925301820963105909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196848809950201213975403939 295273214925301820963105909)
          ·
            refine ⟨27681863899247045715291179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295273214925301820963105909 27681863899247045715291179)
            ·
              refine ⟨41522795848870568572936769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27681863899247045715291179 41522795848870568572936769)
              ·
                refine ⟨31142096886652926429702577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41522795848870568572936769 31142096886652926429702577)
                ·
                  refine ⟨23356572664989694822276933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31142096886652926429702577 23356572664989694822276933)
                  ·
                    refine ⟨4379357374685567779176925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23356572664989694822276933 4379357374685567779176925)
                    ·
                      refine ⟨1642259015507087917191347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379357374685567779176925 1642259015507087917191347)
                      ·
                        rfl

theorem cell23_3198288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_3198288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198288 prefixEnd_3198288 := by exact prefixLift 3198288
  have htrace : WordTrace (prefixWord ++ tailWord_3198288) baseStart_3198288 baseEnd_3198288 := by
    simpa [prefixWord, tailWord_3198288, baseEnd_3198288] using wordTrace_append hprefix tailTrace_3198288
  have hstable : (prefixWord ++ tailWord_3198288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198288).length < 2 ^ (prefixWord ++ tailWord_3198288).sum := by decide
  have hdescent : baseEnd_3198288 < baseStart_3198288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198376 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 5]
def baseStart_3198376 : Nat := 118140960795 + 3198376 * 2 ^ 59
def prefixEnd_3198376 : Nat := 4983230072969 + 3 ^ 40 * 3198376 * 2
def baseEnd_3198376 : Nat := 182478244644964841432327

theorem tailTrace_3198376 : CollatzResearch.WordTrace tailWord_3198376 prefixEnd_3198376 182478244644964841432327 := by
  unfold tailWord_3198376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58327178130418732988795491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77769570840558310651727321 58327178130418732988795491)
  ·
    refine ⟨87490767195628099483193237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58327178130418732988795491 87490767195628099483193237)
    ·
      refine ⟨4101129712295067163274683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87490767195628099483193237 4101129712295067163274683)
      ·
        refine ⟨6151694568442600744912025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101129712295067163274683 6151694568442600744912025)
        ·
          refine ⟨4613770926331950558684019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151694568442600744912025 4613770926331950558684019)
          ·
            refine ⟨6920656389497925838026029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613770926331950558684019 6920656389497925838026029)
            ·
              refine ⟨2595246146061722189259761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6920656389497925838026029 2595246146061722189259761)
              ·
                refine ⟨1946434609546291641944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595246146061722189259761 1946434609546291641944821)
                ·
                  refine ⟨182478244644964841432327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946434609546291641944821 182478244644964841432327)
                  ·
                    rfl

theorem cell23_3198376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 5].length) (baseStart_3198376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198376 prefixEnd_3198376 := by exact prefixLift 3198376
  have htrace : WordTrace (prefixWord ++ tailWord_3198376) baseStart_3198376 baseEnd_3198376 := by
    simpa [prefixWord, tailWord_3198376, baseEnd_3198376] using wordTrace_append hprefix tailTrace_3198376
  have hstable : (prefixWord ++ tailWord_3198376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198376).length < 2 ^ (prefixWord ++ tailWord_3198376).sum := by decide
  have hdescent : baseEnd_3198376 < baseStart_3198376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198412 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3198412 : Nat := 118140960795 + 3198412 * 2 ^ 59
def prefixEnd_3198412 : Nat := 4983230072969 + 3 ^ 40 * 3198412 * 2
def baseEnd_3198412 : Nat := 1642322687108245432040777

theorem tailTrace_3198412 : CollatzResearch.WordTrace tailWord_3198412 prefixEnd_3198412 1642322687108245432040777 := by
  unfold tailWord_3198412
  simp only [CollatzResearch.WordTrace]
  refine ⟨58327834644353522062950745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77770446192471362750600993 58327834644353522062950745)
  ·
    refine ⟨43745875983265141547213059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58327834644353522062950745 43745875983265141547213059)
    ·
      refine ⟨65618813974897712320819589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43745875983265141547213059 65618813974897712320819589)
      ·
        refine ⟨12303527620293321060153673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65618813974897712320819589 12303527620293321060153673)
        ·
          refine ⟨9227645715219990795115255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303527620293321060153673 9227645715219990795115255)
          ·
            refine ⟨13841468572829986192672883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227645715219990795115255 13841468572829986192672883)
            ·
              refine ⟨20762202859244979289009325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841468572829986192672883 20762202859244979289009325)
              ·
                refine ⟨7785826072216867233378497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20762202859244979289009325 7785826072216867233378497)
                ·
                  refine ⟨5839369554162650425033873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785826072216867233378497 5839369554162650425033873)
                  ·
                    refine ⟨4379527165621987818775405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839369554162650425033873 4379527165621987818775405)
                    ·
                      refine ⟨1642322687108245432040777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379527165621987818775405 1642322687108245432040777)
                      ·
                        rfl

theorem cell23_3198412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3198412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198412 prefixEnd_3198412 := by exact prefixLift 3198412
  have htrace : WordTrace (prefixWord ++ tailWord_3198412) baseStart_3198412 baseEnd_3198412 := by
    simpa [prefixWord, tailWord_3198412, baseEnd_3198412] using wordTrace_append hprefix tailTrace_3198412
  have hstable : (prefixWord ++ tailWord_3198412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198412).length < 2 ^ (prefixWord ++ tailWord_3198412).sum := by decide
  have hdescent : baseEnd_3198412 < baseStart_3198412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198492 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_3198492 : Nat := 118140960795 + 3198492 * 2 ^ 59
def prefixEnd_3198492 : Nat := 4983230072969 + 3 ^ 40 * 3198492 * 2
def baseEnd_3198492 : Nat := 547454588520201706346803

theorem tailTrace_3198492 : CollatzResearch.WordTrace tailWord_3198492 prefixEnd_3198492 547454588520201706346803 := by
  unfold tailWord_3198492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329293564208608894406865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77772391418944811859209153 58329293564208608894406865)
  ·
    refine ⟨43746970173156456670805149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58329293564208608894406865 43746970173156456670805149)
    ·
      refine ⟨16405113814933671251551931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43746970173156456670805149 16405113814933671251551931)
      ·
        refine ⟨24607670722400506877327897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16405113814933671251551931 24607670722400506877327897)
        ·
          refine ⟨18455753041800380157995923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24607670722400506877327897 18455753041800380157995923)
          ·
            refine ⟨27683629562700570236993885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18455753041800380157995923 27683629562700570236993885)
            ·
              refine ⟨10381361086012713838872707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27683629562700570236993885 10381361086012713838872707)
              ·
                refine ⟨15572041629019070758309061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10381361086012713838872707 15572041629019070758309061)
                ·
                  refine ⟨2919757805441075767182949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15572041629019070758309061 2919757805441075767182949)
                  ·
                    refine ⟨547454588520201706346803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919757805441075767182949 547454588520201706346803)
                    ·
                      rfl

theorem cell23_3198492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_3198492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198492 prefixEnd_3198492 := by exact prefixLift 3198492
  have htrace : WordTrace (prefixWord ++ tailWord_3198492) baseStart_3198492 baseEnd_3198492 := by
    simpa [prefixWord, tailWord_3198492, baseEnd_3198492] using wordTrace_append hprefix tailTrace_3198492
  have hstable : (prefixWord ++ tailWord_3198492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198492).length < 2 ^ (prefixWord ++ tailWord_3198492).sum := by decide
  have hdescent : baseEnd_3198492 < baseStart_3198492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198495 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3198495 : Nat := 118140960795 + 3198495 * 2 ^ 59
def prefixEnd_3198495 : Nat := 4983230072969 + 3 ^ 40 * 3198495 * 2
def baseEnd_3198495 : Nat := 1642365306002568607302895

theorem tailTrace_3198495 : CollatzResearch.WordTrace tailWord_3198495 prefixEnd_3198495 1642365306002568607302895 := by
  unfold tailWord_3198495
  simp only [CollatzResearch.WordTrace]
  refine ⟨116658696547406349301172939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77772464364937566200781959 116658696547406349301172939)
  ·
    refine ⟨174988044821109523951759409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116658696547406349301172939 174988044821109523951759409)
    ·
      refine ⟨131241033615832142963819557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174988044821109523951759409 131241033615832142963819557)
      ·
        refine ⟨24607693802968526805716167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131241033615832142963819557 24607693802968526805716167)
        ·
          refine ⟨36911540704452790208574251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24607693802968526805716167 36911540704452790208574251)
          ·
            refine ⟨55367311056679185312861377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36911540704452790208574251 55367311056679185312861377)
            ·
              refine ⟨41525483292509388984646033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55367311056679185312861377 41525483292509388984646033)
              ·
                refine ⟨31144112469382041738484525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41525483292509388984646033 31144112469382041738484525)
                ·
                  refine ⟨11679042176018265651931697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31144112469382041738484525 11679042176018265651931697)
                  ·
                    refine ⟨8759281632013699238948773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11679042176018265651931697 8759281632013699238948773)
                    ·
                      refine ⟨1642365306002568607302895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8759281632013699238948773 1642365306002568607302895)
                      ·
                        rfl

theorem cell23_3198495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3198495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198495 prefixEnd_3198495 := by exact prefixLift 3198495
  have htrace : WordTrace (prefixWord ++ tailWord_3198495) baseStart_3198495 baseEnd_3198495 := by
    simpa [prefixWord, tailWord_3198495, baseEnd_3198495] using wordTrace_append hprefix tailTrace_3198495
  have hstable : (prefixWord ++ tailWord_3198495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198495).length < 2 ^ (prefixWord ++ tailWord_3198495).sum := by decide
  have hdescent : baseEnd_3198495 < baseStart_3198495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198519 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_3198519 : Nat := 118140960795 + 3198519 * 2 ^ 59
def prefixEnd_3198519 : Nat := 4983230072969 + 3 ^ 40 * 3198519 * 2
def baseEnd_3198519 : Nat := 1642377629538276513402785

theorem tailTrace_3198519 : CollatzResearch.WordTrace tailWord_3198519 prefixEnd_3198519 1642377629538276513402785 := by
  unfold tailWord_3198519
  simp only [CollatzResearch.WordTrace]
  refine ⟨116659571899319401400046611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77773047932879600933364407 116659571899319401400046611)
  ·
    refine ⟨174989357848979102100069917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116659571899319401400046611 174989357848979102100069917)
    ·
      refine ⟨65621009193367163287526219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174989357848979102100069917 65621009193367163287526219)
      ·
        refine ⟨98431513790050744931289329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65621009193367163287526219 98431513790050744931289329)
        ·
          refine ⟨73823635342538058698466997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98431513790050744931289329 73823635342538058698466997)
          ·
            refine ⟨6920965813362943002981281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73823635342538058698466997 6920965813362943002981281)
            ·
              refine ⟨5190724360022207252235961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6920965813362943002981281 5190724360022207252235961)
              ·
                refine ⟨3893043270016655439176971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190724360022207252235961 3893043270016655439176971)
                ·
                  refine ⟨5839564905024983158765457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893043270016655439176971 5839564905024983158765457)
                  ·
                    refine ⟨4379673678768737369074093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839564905024983158765457 4379673678768737369074093)
                    ·
                      refine ⟨1642377629538276513402785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379673678768737369074093 1642377629538276513402785)
                      ·
                        rfl

theorem cell23_3198519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_3198519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198519 prefixEnd_3198519 := by exact prefixLift 3198519
  have htrace : WordTrace (prefixWord ++ tailWord_3198519) baseStart_3198519 baseEnd_3198519 := by
    simpa [prefixWord, tailWord_3198519, baseEnd_3198519] using wordTrace_append hprefix tailTrace_3198519
  have hstable : (prefixWord ++ tailWord_3198519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198519).length < 2 ^ (prefixWord ++ tailWord_3198519).sum := by decide
  have hdescent : baseEnd_3198519 < baseStart_3198519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198545 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3198545 : Nat := 118140960795 + 3198545 * 2 ^ 59
def prefixEnd_3198545 : Nat := 4983230072969 + 3 ^ 40 * 3198545 * 2
def baseEnd_3198545 : Nat := 1642390980035293411677665

theorem tailTrace_3198545 : CollatzResearch.WordTrace tailWord_3198545 prefixEnd_3198545 1642390980035293411677665 := by
  unfold tailWord_3198545
  simp only [CollatzResearch.WordTrace]
  refine ⟨116660520197225207840493089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77773680131483471893662059 116660520197225207840493089)
  ·
    refine ⟨87495390147918905880369817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116660520197225207840493089 87495390147918905880369817)
    ·
      refine ⟨65621542610939179410277363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87495390147918905880369817 65621542610939179410277363)
      ·
        refine ⟨98432313916408769115416045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65621542610939179410277363 98432313916408769115416045)
        ·
          refine ⟨36912117718653288418281017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98432313916408769115416045 36912117718653288418281017)
          ·
            refine ⟨27684088288989966313710763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36912117718653288418281017 27684088288989966313710763)
            ·
              refine ⟨41526132433484949470566145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27684088288989966313710763 41526132433484949470566145)
              ·
                refine ⟨31144599325113712102924609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41526132433484949470566145 31144599325113712102924609)
                ·
                  refine ⟨23358449493835284077193457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31144599325113712102924609 23358449493835284077193457)
                  ·
                    refine ⟨17518837120376463057895093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23358449493835284077193457 17518837120376463057895093)
                    ·
                      refine ⟨1642390980035293411677665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17518837120376463057895093 1642390980035293411677665)
                      ·
                        rfl

theorem cell23_3198545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3198545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198545 prefixEnd_3198545 := by exact prefixLift 3198545
  have htrace : WordTrace (prefixWord ++ tailWord_3198545) baseStart_3198545 baseEnd_3198545 := by
    simpa [prefixWord, tailWord_3198545, baseEnd_3198545] using wordTrace_append hprefix tailTrace_3198545
  have hstable : (prefixWord ++ tailWord_3198545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198545).length < 2 ^ (prefixWord ++ tailWord_3198545).sum := by decide
  have hdescent : baseEnd_3198545 < baseStart_3198545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198549 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3198549 : Nat := 118140960795 + 3198549 * 2 ^ 59
def prefixEnd_3198549 : Nat := 4983230072969 + 3 ^ 40 * 3198549 * 2
def baseEnd_3198549 : Nat := 1642393033957911396027647

theorem tailTrace_3198549 : CollatzResearch.WordTrace tailWord_3198549 prefixEnd_3198549 1642393033957911396027647 := by
  unfold tailWord_3198549
  simp only [CollatzResearch.WordTrace]
  refine ⟨116660666089210716523638701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77773777392807144349092467 116660666089210716523638701)
  ·
    refine ⟨43747749783454018696364513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116660666089210716523638701 43747749783454018696364513)
    ·
      refine ⟨32810812337590514022273385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43747749783454018696364513 32810812337590514022273385)
      ·
        refine ⟨24608109253192885516705039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32810812337590514022273385 24608109253192885516705039)
        ·
          refine ⟨36912163879789328275057559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24608109253192885516705039 36912163879789328275057559)
          ·
            refine ⟨55368245819683992412586339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36912163879789328275057559 55368245819683992412586339)
            ·
              refine ⟨83052368729525988618879509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55368245819683992412586339 83052368729525988618879509)
              ·
                refine ⟨3893079784196530716509977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83052368729525988618879509 3893079784196530716509977)
                ·
                  refine ⟨2919809838147398037382483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893079784196530716509977 2919809838147398037382483)
                  ·
                    refine ⟨4379714757221097056073725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919809838147398037382483 4379714757221097056073725)
                    ·
                      refine ⟨1642393033957911396027647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4379714757221097056073725 1642393033957911396027647)
                      ·
                        rfl

theorem cell23_3198549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3198549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198549 prefixEnd_3198549 := by exact prefixLift 3198549
  have htrace : WordTrace (prefixWord ++ tailWord_3198549) baseStart_3198549 baseEnd_3198549 := by
    simpa [prefixWord, tailWord_3198549, baseEnd_3198549] using wordTrace_append hprefix tailTrace_3198549
  have hstable : (prefixWord ++ tailWord_3198549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198549).length < 2 ^ (prefixWord ++ tailWord_3198549).sum := by decide
  have hdescent : baseEnd_3198549 < baseStart_3198549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198576 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2]
def baseStart_3198576 : Nat := 118140960795 + 3198576 * 2 ^ 59
def prefixEnd_3198576 : Nat := 4983230072969 + 3 ^ 40 * 3198576 * 2
def baseEnd_3198576 : Nat := 1642406897935582790390023

theorem tailTrace_3198576 : CollatzResearch.WordTrace tailWord_3198576 prefixEnd_3198576 1642406897935582790390023 := by
  unfold tailWord_3198576
  simp only [CollatzResearch.WordTrace]
  refine ⟨58330825430056450067435791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77774433906741933423247721 58330825430056450067435791)
  ·
    refine ⟨87496238145084675101153687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58330825430056450067435791 87496238145084675101153687)
    ·
      refine ⟨131244357217627012651730531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87496238145084675101153687 131244357217627012651730531)
      ·
        refine ⟨196866535826440518977595797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131244357217627012651730531 196866535826440518977595797)
        ·
          refine ⟨9228118866864399327074803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196866535826440518977595797 9228118866864399327074803)
          ·
            refine ⟨13842178300296598990612205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228118866864399327074803 13842178300296598990612205)
            ·
              refine ⟨5190816862611224621479577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13842178300296598990612205 5190816862611224621479577)
              ·
                refine ⟨3893112646958418466109683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190816862611224621479577 3893112646958418466109683)
                ·
                  refine ⟨5839668970437627699164525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893112646958418466109683 5839668970437627699164525)
                  ·
                    refine ⟨2189875863914110387186697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5839668970437627699164525 2189875863914110387186697)
                    ·
                      refine ⟨1642406897935582790390023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189875863914110387186697 1642406897935582790390023)
                      ·
                        rfl

theorem cell23_3198576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2].length) (baseStart_3198576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198576 prefixEnd_3198576 := by exact prefixLift 3198576
  have htrace : WordTrace (prefixWord ++ tailWord_3198576) baseStart_3198576 baseEnd_3198576 := by
    simpa [prefixWord, tailWord_3198576, baseEnd_3198576] using wordTrace_append hprefix tailTrace_3198576
  have hstable : (prefixWord ++ tailWord_3198576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198576).length < 2 ^ (prefixWord ++ tailWord_3198576).sum := by decide
  have hdescent : baseEnd_3198576 < baseStart_3198576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198589 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_3198589 : Nat := 118140960795 + 3198589 * 2 ^ 59
def prefixEnd_3198589 : Nat := 4983230072969 + 3 ^ 40 * 3198589 * 2
def baseEnd_3198589 : Nat := 1642413573184091239527463

theorem tailTrace_3198589 : CollatzResearch.WordTrace tailWord_3198589 prefixEnd_3198589 1642413573184091239527463 := by
  unfold tailWord_3198589
  simp only [CollatzResearch.WordTrace]
  refine ⟨116662125009065803355094821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77774750006043868903396547 116662125009065803355094821)
  ·
    refine ⟨21874148439199838129080279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116662125009065803355094821 21874148439199838129080279)
    ·
      refine ⟨32811222658799757193620419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21874148439199838129080279 32811222658799757193620419)
      ·
        refine ⟨49216833988199635790430629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32811222658799757193620419 49216833988199635790430629)
        ·
          refine ⟨9228156372787431710705743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49216833988199635790430629 9228156372787431710705743)
          ·
            refine ⟨13842234559181147566058615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228156372787431710705743 13842234559181147566058615)
            ·
              refine ⟨20763351838771721349087923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842234559181147566058615 20763351838771721349087923)
              ·
                refine ⟨31145027758157582023631885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20763351838771721349087923 31145027758157582023631885)
                ·
                  refine ⟨11679385409309093258861957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31145027758157582023631885 11679385409309093258861957)
                  ·
                    refine ⟨2189884764245454986036617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11679385409309093258861957 2189884764245454986036617)
                    ·
                      refine ⟨1642413573184091239527463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189884764245454986036617 1642413573184091239527463)
                      ·
                        rfl

theorem cell23_3198589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_3198589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198589 prefixEnd_3198589 := by exact prefixLift 3198589
  have htrace : WordTrace (prefixWord ++ tailWord_3198589) baseStart_3198589 baseEnd_3198589 := by
    simpa [prefixWord, tailWord_3198589, baseEnd_3198589] using wordTrace_append hprefix tailTrace_3198589
  have hstable : (prefixWord ++ tailWord_3198589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198589).length < 2 ^ (prefixWord ++ tailWord_3198589).sum := by decide
  have hdescent : baseEnd_3198589 < baseStart_3198589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198593 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_3198593 : Nat := 118140960795 + 3198593 * 2 ^ 59
def prefixEnd_3198593 : Nat := 4983230072969 + 3 ^ 40 * 3198593 * 2
def baseEnd_3198593 : Nat := 1642415627106709223877445

theorem tailTrace_3198593 : CollatzResearch.WordTrace tailWord_3198593 prefixEnd_3198593 1642415627106709223877445 := by
  unfold tailWord_3198593
  simp only [CollatzResearch.WordTrace]
  refine ⟨116662270901051312038240433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77774847267367541358826955 116662270901051312038240433)
  ·
    refine ⟨87496703175788484028680325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116662270901051312038240433 87496703175788484028680325)
    ·
      refine ⟨16405631845460340755377561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87496703175788484028680325 16405631845460340755377561)
      ·
        refine ⟨12304223884095255566533171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16405631845460340755377561 12304223884095255566533171)
        ·
          refine ⟨18456335826142883349799757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12304223884095255566533171 18456335826142883349799757)
          ·
            refine ⟨6921125934803581256174909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18456335826142883349799757 6921125934803581256174909)
            ·
              refine ⟨2595422225551342971065591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6921125934803581256174909 2595422225551342971065591)
              ·
                refine ⟨3893133338327014456598387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595422225551342971065591 3893133338327014456598387)
                ·
                  refine ⟨5839700007490521684897581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893133338327014456598387 5839700007490521684897581)
                  ·
                    refine ⟨2189887502808945631836593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5839700007490521684897581 2189887502808945631836593)
                    ·
                      refine ⟨1642415627106709223877445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189887502808945631836593 1642415627106709223877445)
                      ·
                        rfl

theorem cell23_3198593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_3198593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198593 prefixEnd_3198593 := by exact prefixLift 3198593
  have htrace : WordTrace (prefixWord ++ tailWord_3198593) baseStart_3198593 baseEnd_3198593 := by
    simpa [prefixWord, tailWord_3198593, baseEnd_3198593] using wordTrace_append hprefix tailTrace_3198593
  have hstable : (prefixWord ++ tailWord_3198593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198593).length < 2 ^ (prefixWord ++ tailWord_3198593).sum := by decide
  have hdescent : baseEnd_3198593 < baseStart_3198593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198623 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3198623 : Nat := 118140960795 + 3198623 * 2 ^ 59
def prefixEnd_3198623 : Nat := 4983230072969 + 3 ^ 40 * 3198623 * 2
def baseEnd_3198623 : Nat := 1642431031526344106502307

theorem tailTrace_3198623 : CollatzResearch.WordTrace tailWord_3198623 prefixEnd_3198623 1642431031526344106502307 := by
  unfold tailWord_3198623
  simp only [CollatzResearch.WordTrace]
  refine ⟨116663365090942627161832523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77775576727295084774555015 116663365090942627161832523)
  ·
    refine ⟨174995047636413940742748785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116663365090942627161832523 174995047636413940742748785)
    ·
      refine ⟨131246285727310455557061589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174995047636413940742748785 131246285727310455557061589)
      ·
        refine ⟨3076084821733838802118631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 131246285727310455557061589 3076084821733838802118631)
        ·
          refine ⟨4614127232600758203177947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076084821733838802118631 4614127232600758203177947)
          ·
            refine ⟨6921190848901137304766921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614127232600758203177947 6921190848901137304766921)
            ·
              refine ⟨5190893136675852978575191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921190848901137304766921 5190893136675852978575191)
              ·
                refine ⟨7786339705013779467862787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190893136675852978575191 7786339705013779467862787)
                ·
                  refine ⟨11679509557520669201794181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786339705013779467862787 11679509557520669201794181)
                  ·
                    refine ⟨2189908042035125475336409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11679509557520669201794181 2189908042035125475336409)
                    ·
                      refine ⟨1642431031526344106502307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189908042035125475336409 1642431031526344106502307)
                      ·
                        rfl

theorem cell23_3198623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3198623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198623 prefixEnd_3198623 := by exact prefixLift 3198623
  have htrace : WordTrace (prefixWord ++ tailWord_3198623) baseStart_3198623 baseEnd_3198623 := by
    simpa [prefixWord, tailWord_3198623, baseEnd_3198623] using wordTrace_append hprefix tailTrace_3198623
  have hstable : (prefixWord ++ tailWord_3198623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198623).length < 2 ^ (prefixWord ++ tailWord_3198623).sum := by decide
  have hdescent : baseEnd_3198623 < baseStart_3198623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198635 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_3198635 : Nat := 118140960795 + 3198635 * 2 ^ 59
def prefixEnd_3198635 : Nat := 4983230072969 + 3 ^ 40 * 3198635 * 2
def baseEnd_3198635 : Nat := 1642437193294198059552251

theorem tailTrace_3198635 : CollatzResearch.WordTrace tailWord_3198635 prefixEnd_3198635 1642437193294198059552251 := by
  unfold tailWord_3198635
  simp only [CollatzResearch.WordTrace]
  refine ⟨116663802766899153211269359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77775868511266102140846239 116663802766899153211269359)
  ·
    refine ⟨174995704150348729816904039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116663802766899153211269359 174995704150348729816904039)
    ·
      refine ⟨262493556225523094725356059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174995704150348729816904039 262493556225523094725356059)
      ·
        refine ⟨393740334338284642088034089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262493556225523094725356059 393740334338284642088034089)
        ·
          refine ⟨295305250753713481566025567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393740334338284642088034089 295305250753713481566025567)
          ·
            refine ⟨442957876130570222349038351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295305250753713481566025567 442957876130570222349038351)
            ·
              refine ⟨664436814195855333523557527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442957876130570222349038351 664436814195855333523557527)
              ·
                refine ⟨996655221293783000285336291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664436814195855333523557527 996655221293783000285336291)
                ·
                  refine ⟨1494982831940674500428004437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996655221293783000285336291 1494982831940674500428004437)
                  ·
                    refine ⟨17519330061804779301890677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1494982831940674500428004437 17519330061804779301890677)
                    ·
                      refine ⟨1642437193294198059552251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17519330061804779301890677 1642437193294198059552251)
                      ·
                        rfl

theorem cell23_3198635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_3198635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198635 prefixEnd_3198635 := by exact prefixLift 3198635
  have htrace : WordTrace (prefixWord ++ tailWord_3198635) baseStart_3198635 baseEnd_3198635 := by
    simpa [prefixWord, tailWord_3198635, baseEnd_3198635] using wordTrace_append hprefix tailTrace_3198635
  have hstable : (prefixWord ++ tailWord_3198635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198635).length < 2 ^ (prefixWord ++ tailWord_3198635).sum := by decide
  have hdescent : baseEnd_3198635 < baseStart_3198635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198679 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_3198679 : Nat := 118140960795 + 3198679 * 2 ^ 59
def prefixEnd_3198679 : Nat := 4983230072969 + 3 ^ 40 * 3198679 * 2
def baseEnd_3198679 : Nat := 1642459786442995887402049

theorem tailTrace_3198679 : CollatzResearch.WordTrace tailWord_3198679 prefixEnd_3198679 1642459786442995887402049 := by
  unfold tailWord_3198679
  simp only [CollatzResearch.WordTrace]
  refine ⟨116665407578739748725871091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77776938385826499150580727 116665407578739748725871091)
  ·
    refine ⟨174998111368109623088806637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116665407578739748725871091 174998111368109623088806637)
    ·
      refine ⟨65624291763041108658302489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174998111368109623088806637 65624291763041108658302489)
      ·
        refine ⟨49218218822280831493726867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65624291763041108658302489 49218218822280831493726867)
        ·
          refine ⟨73827328233421247240590301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49218218822280831493726867 73827328233421247240590301)
          ·
            refine ⟨27685248087532967715221363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73827328233421247240590301 27685248087532967715221363)
            ·
              refine ⟨41527872131299451572832045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685248087532967715221363 41527872131299451572832045)
              ·
                refine ⟨15572952049237294339812017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41527872131299451572832045 15572952049237294339812017)
                ·
                  refine ⟨11679714036927970754859013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15572952049237294339812017 11679714036927970754859013)
                  ·
                    refine ⟨2189946381923994516536065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11679714036927970754859013 2189946381923994516536065)
                    ·
                      refine ⟨1642459786442995887402049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189946381923994516536065 1642459786442995887402049)
                      ·
                        rfl

theorem cell23_3198679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_3198679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198679 prefixEnd_3198679 := by exact prefixLift 3198679
  have htrace : WordTrace (prefixWord ++ tailWord_3198679) baseStart_3198679 baseEnd_3198679 := by
    simpa [prefixWord, tailWord_3198679, baseEnd_3198679] using wordTrace_append hprefix tailTrace_3198679
  have hstable : (prefixWord ++ tailWord_3198679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198679).length < 2 ^ (prefixWord ++ tailWord_3198679).sum := by decide
  have hdescent : baseEnd_3198679 < baseStart_3198679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198692 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3198692 : Nat := 118140960795 + 3198692 * 2 ^ 59
def prefixEnd_3198692 : Nat := 4983230072969 + 3 ^ 40 * 3198692 * 2
def baseEnd_3198692 : Nat := 1642466461691504336539489

theorem tailTrace_3198692 : CollatzResearch.WordTrace tailWord_3198692 prefixEnd_3198692 1642466461691504336539489 := by
  unfold tailWord_3198692
  simp only [CollatzResearch.WordTrace]
  refine ⟨58332940863846325973047165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77777254485128434630729553 58332940863846325973047165)
  ·
    refine ⟨21874852823942372239892687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58332940863846325973047165 21874852823942372239892687)
    ·
      refine ⟨32812279235913558359839031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21874852823942372239892687 32812279235913558359839031)
      ·
        refine ⟨49218418853870337539758547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32812279235913558359839031 49218418853870337539758547)
        ·
          refine ⟨73827628280805506309637821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49218418853870337539758547 73827628280805506309637821)
          ·
            refine ⟨27685360605302064866114183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73827628280805506309637821 27685360605302064866114183)
            ·
              refine ⟨41528040907953097299171275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685360605302064866114183 41528040907953097299171275)
              ·
                refine ⟨62292061361929645948756913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41528040907953097299171275 62292061361929645948756913)
                ·
                  refine ⟨46719046021447234461567685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62292061361929645948756913 46719046021447234461567685)
                  ·
                    refine ⟨8759821129021356461543941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46719046021447234461567685 8759821129021356461543941)
                    ·
                      refine ⟨1642466461691504336539489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8759821129021356461543941 1642466461691504336539489)
                      ·
                        rfl

theorem cell23_3198692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3198692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198692 prefixEnd_3198692 := by exact prefixLift 3198692
  have htrace : WordTrace (prefixWord ++ tailWord_3198692) baseStart_3198692 baseEnd_3198692 := by
    simpa [prefixWord, tailWord_3198692, baseEnd_3198692] using wordTrace_append hprefix tailTrace_3198692
  have hstable : (prefixWord ++ tailWord_3198692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198692).length < 2 ^ (prefixWord ++ tailWord_3198692).sum := by decide
  have hdescent : baseEnd_3198692 < baseStart_3198692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198702 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_3198702 : Nat := 118140960795 + 3198702 * 2 ^ 59
def prefixEnd_3198702 : Nat := 4983230072969 + 3 ^ 40 * 3198702 * 2
def baseEnd_3198702 : Nat := 182496844055338810823827

theorem tailTrace_3198702 : CollatzResearch.WordTrace tailWord_3198702 prefixEnd_3198702 182496844055338810823827 := by
  unfold tailWord_3198702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583280807207052956744795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77777497638437615769305573 14583280807207052956744795)
  ·
    refine ⟨21874921210810579435117193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583280807207052956744795 21874921210810579435117193)
    ·
      refine ⟨16406190908107934576337895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21874921210810579435117193 16406190908107934576337895)
      ·
        refine ⟨24609286362161901864506843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16406190908107934576337895 24609286362161901864506843)
        ·
          refine ⟨36913929543242852796760265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24609286362161901864506843 36913929543242852796760265)
          ·
            refine ⟨27685447157432139597570199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36913929543242852796760265 27685447157432139597570199)
            ·
              refine ⟨41528170736148209396355299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685447157432139597570199 41528170736148209396355299)
              ·
                refine ⟨62292256104222314094532949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41528170736148209396355299 62292256104222314094532949)
                ·
                  refine ⟨182496844055338810823827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62292256104222314094532949 182496844055338810823827)
                  ·
                    rfl

theorem cell23_3198702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_3198702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198702 prefixEnd_3198702 := by exact prefixLift 3198702
  have htrace : WordTrace (prefixWord ++ tailWord_3198702) baseStart_3198702 baseEnd_3198702 := by
    simpa [prefixWord, tailWord_3198702, baseEnd_3198702] using wordTrace_append hprefix tailTrace_3198702
  have hstable : (prefixWord ++ tailWord_3198702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198702).length < 2 ^ (prefixWord ++ tailWord_3198702).sum := by decide
  have hdescent : baseEnd_3198702 < baseStart_3198702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198739 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 5, 2]
def baseStart_3198739 : Nat := 118140960795 + 3198739 * 2 ^ 59
def prefixEnd_3198739 : Nat := 4983230072969 + 3 ^ 40 * 3198739 * 2
def baseEnd_3198739 : Nat := 1642490595282265652651773

theorem tailTrace_3198739 : CollatzResearch.WordTrace tailWord_3198739 prefixEnd_3198739 1642490595282265652651773 := by
  unfold tailWord_3198739
  simp only [CollatzResearch.WordTrace]
  refine ⟨116667595958522378973055271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77778397305681585982036847 116667595958522378973055271)
  ·
    refine ⟨175001393937783568459582907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116667595958522378973055271 175001393937783568459582907)
    ·
      refine ⟨262502090906675352689374361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175001393937783568459582907 262502090906675352689374361)
      ·
        refine ⟨196876568180006514517030771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262502090906675352689374361 196876568180006514517030771)
        ·
          refine ⟨295314852270009771775546157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196876568180006514517030771 295314852270009771775546157)
          ·
            refine ⟨110743069601253664415829809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295314852270009771775546157 110743069601253664415829809)
            ·
              refine ⟨83057302200940248311872357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110743069601253664415829809 83057302200940248311872357)
              ·
                refine ⟨15573244162676296558476067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83057302200940248311872357 15573244162676296558476067)
                ·
                  refine ⟨23359866244014444837714101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15573244162676296558476067 23359866244014444837714101)
                  ·
                    refine ⟨2189987460376354203535697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23359866244014444837714101 2189987460376354203535697)
                    ·
                      refine ⟨1642490595282265652651773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2189987460376354203535697 1642490595282265652651773)
                      ·
                        rfl

theorem cell23_3198739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5, 2].length) (baseStart_3198739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198739 prefixEnd_3198739 := by exact prefixLift 3198739
  have htrace : WordTrace (prefixWord ++ tailWord_3198739) baseStart_3198739 baseEnd_3198739 := by
    simpa [prefixWord, tailWord_3198739, baseEnd_3198739] using wordTrace_append hprefix tailTrace_3198739
  have hstable : (prefixWord ++ tailWord_3198739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198739).length < 2 ^ (prefixWord ++ tailWord_3198739).sum := by decide
  have hdescent : baseEnd_3198739 < baseStart_3198739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198780 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_3198780 : Nat := 118140960795 + 3198780 * 2 ^ 59
def prefixEnd_3198780 : Nat := 4983230072969 + 3 ^ 40 * 3198780 * 2
def baseEnd_3198780 : Nat := 1642511647989099992239085

theorem tailTrace_3198780 : CollatzResearch.WordTrace tailWord_3198780 prefixEnd_3198780 1642511647989099992239085 := by
  unfold tailWord_3198780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58334545675686921487648897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77779394234249228650198529 58334545675686921487648897)
  ·
    refine ⟨43750909256765191115736673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58334545675686921487648897 43750909256765191115736673)
    ·
      refine ⟨32813181942573893336802505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43750909256765191115736673 32813181942573893336802505)
      ·
        refine ⟨24609886456930420002601879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32813181942573893336802505 24609886456930420002601879)
        ·
          refine ⟨36914829685395630003902819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24609886456930420002601879 36914829685395630003902819)
          ·
            refine ⟨55372244528093445005854229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36914829685395630003902819 55372244528093445005854229)
            ·
              refine ⟨2595573962254380234649417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55372244528093445005854229 2595573962254380234649417)
              ·
                refine ⟨1946680471690785175987063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595573962254380234649417 1946680471690785175987063)
                ·
                  refine ⟨2920020707536177763980595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946680471690785175987063 2920020707536177763980595)
                  ·
                    refine ⟨4380031061304266645970893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2920020707536177763980595 4380031061304266645970893)
                    ·
                      refine ⟨1642511647989099992239085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380031061304266645970893 1642511647989099992239085)
                      ·
                        rfl

theorem cell23_3198780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_3198780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198780 prefixEnd_3198780 := by exact prefixLift 3198780
  have htrace : WordTrace (prefixWord ++ tailWord_3198780) baseStart_3198780 baseEnd_3198780 := by
    simpa [prefixWord, tailWord_3198780, baseEnd_3198780] using wordTrace_append hprefix tailTrace_3198780
  have hstable : (prefixWord ++ tailWord_3198780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198780).length < 2 ^ (prefixWord ++ tailWord_3198780).sum := by decide
  have hdescent : baseEnd_3198780 < baseStart_3198780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198789 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_3198789 : Nat := 118140960795 + 3198789 * 2 ^ 59
def prefixEnd_3198789 : Nat := 4983230072969 + 3 ^ 40 * 3198789 * 2
def baseEnd_3198789 : Nat := 1642516269314990457026543

theorem tailTrace_3198789 : CollatzResearch.WordTrace tailWord_3198789 prefixEnd_3198789 1642516269314990457026543 := by
  unfold tailWord_3198789
  simp only [CollatzResearch.WordTrace]
  refine ⟨116669419608341237512375421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77779613072227491674916947 116669419608341237512375421)
  ·
    refine ⟨43751032353127964067140783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116669419608341237512375421 43751032353127964067140783)
    ·
      refine ⟨65626548529691946100711175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43751032353127964067140783 65626548529691946100711175)
      ·
        refine ⟨98439822794537919151066763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65626548529691946100711175 98439822794537919151066763)
        ·
          refine ⟨147659734191806878726600145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98439822794537919151066763 147659734191806878726600145)
          ·
            refine ⟨110744800643855159044950109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147659734191806878726600145 110744800643855159044950109)
            ·
              refine ⟨41529300241445684641856291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110744800643855159044950109 41529300241445684641856291)
              ·
                refine ⟨62293950362168526962784437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41529300241445684641856291 62293950362168526962784437)
                ·
                  refine ⟨5840057846453299402761041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62293950362168526962784437 5840057846453299402761041)
                  ·
                    refine ⟨4380043384839974552070781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5840057846453299402761041 4380043384839974552070781)
                    ·
                      refine ⟨1642516269314990457026543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380043384839974552070781 1642516269314990457026543)
                      ·
                        rfl

theorem cell23_3198789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_3198789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198789 prefixEnd_3198789 := by exact prefixLift 3198789
  have htrace : WordTrace (prefixWord ++ tailWord_3198789) baseStart_3198789 baseEnd_3198789 := by
    simpa [prefixWord, tailWord_3198789, baseEnd_3198789] using wordTrace_append hprefix tailTrace_3198789
  have hstable : (prefixWord ++ tailWord_3198789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198789).length < 2 ^ (prefixWord ++ tailWord_3198789).sum := by decide
  have hdescent : baseEnd_3198789 < baseStart_3198789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198796 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_3198796 : Nat := 118140960795 + 3198796 * 2 ^ 59
def prefixEnd_3198796 : Nat := 4983230072969 + 3 ^ 40 * 3198796 * 2
def baseEnd_3198796 : Nat := 547506621226523976546337

theorem tailTrace_3198796 : CollatzResearch.WordTrace tailWord_3198796 prefixEnd_3198796 547506621226523976546337 := by
  unfold tailWord_3198796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58334837459657938853940121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77779783279543918471920161 58334837459657938853940121)
  ·
    refine ⟨43751128094743454140455091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58334837459657938853940121 43751128094743454140455091)
    ·
      refine ⟨65626692142115181210682637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43751128094743454140455091 65626692142115181210682637)
      ·
        refine ⟨24610009553293192954005989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65626692142115181210682637 24610009553293192954005989)
        ·
          refine ⟨4614376791242473678876123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24610009553293192954005989 4614376791242473678876123)
          ·
            refine ⟨6921565186863710518314185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614376791242473678876123 6921565186863710518314185)
            ·
              refine ⟨5191173890147782888735639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921565186863710518314185 5191173890147782888735639)
              ·
                refine ⟨7786760835221674333103459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191173890147782888735639 7786760835221674333103459)
                ·
                  refine ⟨11680141252832511499655189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786760835221674333103459 11680141252832511499655189)
                  ·
                    refine ⟨547506621226523976546337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11680141252832511499655189 547506621226523976546337)
                    ·
                      rfl

theorem cell23_3198796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_3198796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198796 prefixEnd_3198796 := by exact prefixLift 3198796
  have htrace : WordTrace (prefixWord ++ tailWord_3198796) baseStart_3198796 baseEnd_3198796 := by
    simpa [prefixWord, tailWord_3198796, baseEnd_3198796] using wordTrace_append hprefix tailTrace_3198796
  have hstable : (prefixWord ++ tailWord_3198796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198796).length < 2 ^ (prefixWord ++ tailWord_3198796).sum := by decide
  have hdescent : baseEnd_3198796 < baseStart_3198796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198809 : List Nat := [1, 2, 1, 2, 2, 3, 5, 7]
def baseStart_3198809 : Nat := 118140960795 + 3198809 * 2 ^ 59
def prefixEnd_3198809 : Nat := 4983230072969 + 3 ^ 40 * 3198809 * 2
def baseEnd_3198809 : Nat := 60834316256595569584313

theorem tailTrace_3198809 : CollatzResearch.WordTrace tailWord_3198809 prefixEnd_3198809 60834316256595569584313 := by
  unfold tailWord_3198809
  simp only [CollatzResearch.WordTrace]
  refine ⟨116670149068268780928103481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77780099378845853952068987 116670149068268780928103481)
  ·
    refine ⟨87502611801201585696077611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116670149068268780928103481 87502611801201585696077611)
    ·
      refine ⟨131253917701802378544116417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87502611801201585696077611 131253917701802378544116417)
      ·
        refine ⟨98440438276351783908087313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131253917701802378544116417 98440438276351783908087313)
        ·
          refine ⟨73830328707263837931065485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98440438276351783908087313 73830328707263837931065485)
          ·
            refine ⟨27686373265223939224149557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73830328707263837931065485 27686373265223939224149557)
            ·
              refine ⟨2595597493614744302264021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27686373265223939224149557 2595597493614744302264021)
              ·
                refine ⟨60834316256595569584313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2595597493614744302264021 60834316256595569584313)
                ·
                  rfl

theorem cell23_3198809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 7].length) (baseStart_3198809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198809 prefixEnd_3198809 := by exact prefixLift 3198809
  have htrace : WordTrace (prefixWord ++ tailWord_3198809) baseStart_3198809 baseEnd_3198809 := by
    simpa [prefixWord, tailWord_3198809, baseEnd_3198809] using wordTrace_append hprefix tailTrace_3198809
  have hstable : (prefixWord ++ tailWord_3198809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198809).length < 2 ^ (prefixWord ++ tailWord_3198809).sum := by decide
  have hdescent : baseEnd_3198809 < baseStart_3198809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198820 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_3198820 : Nat := 118140960795 + 3198820 * 2 ^ 59
def prefixEnd_3198820 : Nat := 4983230072969 + 3 ^ 40 * 3198820 * 2
def baseEnd_3198820 : Nat := 1642532187215279835738901

theorem tailTrace_3198820 : CollatzResearch.WordTrace tailWord_3198820 prefixEnd_3198820 1642532187215279835738901 := by
  unfold tailWord_3198820
  simp only [CollatzResearch.WordTrace]
  refine ⟨58335275135614464903376957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77780366847485953204502609 58335275135614464903376957)
  ·
    refine ⟨21875728175855424338766359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58335275135614464903376957 21875728175855424338766359)
    ·
      refine ⟨32813592263783136508149539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21875728175855424338766359 32813592263783136508149539)
      ·
        refine ⟨49220388395674704762224309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32813592263783136508149539 49220388395674704762224309)
        ·
          refine ⟨4614411412094503571458529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49220388395674704762224309 4614411412094503571458529)
          ·
            refine ⟨3460808559070877678593897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4614411412094503571458529 3460808559070877678593897)
            ·
              refine ⟨2595606419303158258945423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460808559070877678593897 2595606419303158258945423)
              ·
                refine ⟨3893409628954737388418135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595606419303158258945423 3893409628954737388418135)
                ·
                  refine ⟨5840114443432106082627203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893409628954737388418135 5840114443432106082627203)
                  ·
                    refine ⟨8760171665148159123940805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840114443432106082627203 8760171665148159123940805)
                    ·
                      refine ⟨1642532187215279835738901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8760171665148159123940805 1642532187215279835738901)
                      ·
                        rfl

theorem cell23_3198820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_3198820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198820 prefixEnd_3198820 := by exact prefixLift 3198820
  have htrace : WordTrace (prefixWord ++ tailWord_3198820) baseStart_3198820 baseEnd_3198820 := by
    simpa [prefixWord, tailWord_3198820, baseEnd_3198820] using wordTrace_append hprefix tailTrace_3198820
  have hstable : (prefixWord ++ tailWord_3198820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198820).length < 2 ^ (prefixWord ++ tailWord_3198820).sum := by decide
  have hdescent : baseEnd_3198820 < baseStart_3198820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198826 : List Nat := [3, 1, 3, 4, 1, 1, 10]
def baseStart_3198826 : Nat := 118140960795 + 3198826 * 2 ^ 59
def prefixEnd_3198826 : Nat := 4983230072969 + 3 ^ 40 * 3198826 * 2
def baseEnd_3198826 : Nat := 20278213186409960645233

theorem tailTrace_3198826 : CollatzResearch.WordTrace tailWord_3198826 prefixEnd_3198826 20278213186409960645233 := by
  unfold tailWord_3198826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29167692277301798207868083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77780512739471461887648221 29167692277301798207868083)
  ·
    refine ⟨43751538415952697311802125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29167692277301798207868083 43751538415952697311802125)
    ·
      refine ⟨16406826905982261491925797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43751538415952697311802125 16406826905982261491925797)
      ·
        refine ⟨3076280044871674029736087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16406826905982261491925797 3076280044871674029736087)
        ·
          refine ⟨4614420067307511044604131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076280044871674029736087 4614420067307511044604131)
          ·
            refine ⟨6921630100961266566906197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614420067307511044604131 6921630100961266566906197)
            ·
              refine ⟨20278213186409960645233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6921630100961266566906197 20278213186409960645233)
              ·
                rfl

theorem cell23_3198826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 10].length) (baseStart_3198826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198826 prefixEnd_3198826 := by exact prefixLift 3198826
  have htrace : WordTrace (prefixWord ++ tailWord_3198826) baseStart_3198826 baseEnd_3198826 := by
    simpa [prefixWord, tailWord_3198826, baseEnd_3198826] using wordTrace_append hprefix tailTrace_3198826
  have hstable : (prefixWord ++ tailWord_3198826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198826).length < 2 ^ (prefixWord ++ tailWord_3198826).sum := by decide
  have hdescent : baseEnd_3198826 < baseStart_3198826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198830 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3198830 : Nat := 118140960795 + 3198830 * 2 ^ 59
def prefixEnd_3198830 : Nat := 4983230072969 + 3 ^ 40 * 3198830 * 2
def baseEnd_3198830 : Nat := 547512440673941598871285

theorem tailTrace_3198830 : CollatzResearch.WordTrace tailWord_3198830 prefixEnd_3198830 547512440673941598871285 := by
  unfold tailWord_3198830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583864375149087689327243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77780610000795134343078629 14583864375149087689327243)
  ·
    refine ⟨21875796562723631533990865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583864375149087689327243 21875796562723631533990865)
    ·
      refine ⟨16406847422042723650493149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21875796562723631533990865 16406847422042723650493149)
      ·
        refine ⟨6152567783266021368934931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16406847422042723650493149 6152567783266021368934931)
        ·
          refine ⟨9228851674899032053402397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152567783266021368934931 9228851674899032053402397)
          ·
            refine ⟨3460819378087137020025899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9228851674899032053402397 3460819378087137020025899)
            ·
              refine ⟨5191229067130705530038849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460819378087137020025899 5191229067130705530038849)
              ·
                refine ⟨3893421800348029147529137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191229067130705530038849 3893421800348029147529137)
                ·
                  refine ⟨2920066350261021860646853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893421800348029147529137 2920066350261021860646853)
                  ·
                    refine ⟨547512440673941598871285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920066350261021860646853 547512440673941598871285)
                    ·
                      rfl

theorem cell23_3198830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3198830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198830 prefixEnd_3198830 := by exact prefixLift 3198830
  have htrace : WordTrace (prefixWord ++ tailWord_3198830) baseStart_3198830 baseEnd_3198830 := by
    simpa [prefixWord, tailWord_3198830, baseEnd_3198830] using wordTrace_append hprefix tailTrace_3198830
  have hstable : (prefixWord ++ tailWord_3198830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198830).length < 2 ^ (prefixWord ++ tailWord_3198830).sum := by decide
  have hdescent : baseEnd_3198830 < baseStart_3198830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198866 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3198866 : Nat := 118140960795 + 3198866 * 2 ^ 59
def prefixEnd_3198866 : Nat := 4983230072969 + 3 ^ 40 * 3198866 * 2
def baseEnd_3198866 : Nat := 1642555807325386655763689

theorem tailTrace_3198866 : CollatzResearch.WordTrace tailWord_3198866 prefixEnd_3198866 1642555807325386655763689 := by
  unfold tailWord_3198866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29168057007265569915732113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77781485352708186441952301 29168057007265569915732113)
  ·
    refine ⟨21876042755449177436799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29168057007265569915732113 21876042755449177436799085)
    ·
      refine ⟨8203516033293441538799657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21876042755449177436799085 8203516033293441538799657)
      ·
        refine ⟨6152637024970081154099743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8203516033293441538799657 6152637024970081154099743)
        ·
          refine ⟨9228955537455121731149615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152637024970081154099743 9228955537455121731149615)
          ·
            refine ⟨13843433306182682596724423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228955537455121731149615 13843433306182682596724423)
            ·
              refine ⟨20765149959274023895086635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843433306182682596724423 20765149959274023895086635)
              ·
                refine ⟨31147724938911035842629953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20765149959274023895086635 31147724938911035842629953)
                ·
                  refine ⟨23360793704183276881972465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31147724938911035842629953 23360793704183276881972465)
                  ·
                    refine ⟨17520595278137457661479349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23360793704183276881972465 17520595278137457661479349)
                    ·
                      refine ⟨1642555807325386655763689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17520595278137457661479349 1642555807325386655763689)
                      ·
                        rfl

theorem cell23_3198866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3198866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198866 prefixEnd_3198866 := by exact prefixLift 3198866
  have htrace : WordTrace (prefixWord ++ tailWord_3198866) baseStart_3198866 baseEnd_3198866 := by
    simpa [prefixWord, tailWord_3198866, baseEnd_3198866] using wordTrace_append hprefix tailTrace_3198866
  have hstable : (prefixWord ++ tailWord_3198866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198866).length < 2 ^ (prefixWord ++ tailWord_3198866).sum := by decide
  have hdescent : baseEnd_3198866 < baseStart_3198866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198889 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3198889 : Nat := 118140960795 + 3198889 * 2 ^ 59
def prefixEnd_3198889 : Nat := 4983230072969 + 3 ^ 40 * 3198889 * 2
def baseEnd_3198889 : Nat := 1642567617380440065776083

theorem tailTrace_3198889 : CollatzResearch.WordTrace tailWord_3198889 prefixEnd_3198889 1642567617380440065776083 := by
  unfold tailWord_3198889
  simp only [CollatzResearch.WordTrace]
  refine ⟨116673066907978954591015721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77782044605319303060677147 116673066907978954591015721)
  ·
    refine ⟨87504800180984215943261791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116673066907978954591015721 87504800180984215943261791)
    ·
      refine ⟨131257200271476323914892687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87504800180984215943261791 131257200271476323914892687)
      ·
        refine ⟨196885800407214485872339031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131257200271476323914892687 196885800407214485872339031)
        ·
          refine ⟨295328700610821728808508547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196885800407214485872339031 295328700610821728808508547)
          ·
            refine ⟨442993050916232593212762821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295328700610821728808508547 442993050916232593212762821)
            ·
              refine ⟨83061197046793611227393029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442993050916232593212762821 83061197046793611227393029)
              ·
                refine ⟨15573974446273802105136193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83061197046793611227393029 15573974446273802105136193)
                ·
                  refine ⟨11680480834705351578852145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15573974446273802105136193 11680480834705351578852145)
                  ·
                    refine ⟨8760360626029013684139109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11680480834705351578852145 8760360626029013684139109)
                    ·
                      refine ⟨1642567617380440065776083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8760360626029013684139109 1642567617380440065776083)
                      ·
                        rfl

theorem cell23_3198889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3198889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198889 prefixEnd_3198889 := by exact prefixLift 3198889
  have htrace : WordTrace (prefixWord ++ tailWord_3198889) baseStart_3198889 baseEnd_3198889 := by
    simpa [prefixWord, tailWord_3198889, baseEnd_3198889] using wordTrace_append hprefix tailTrace_3198889
  have hstable : (prefixWord ++ tailWord_3198889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198889).length < 2 ^ (prefixWord ++ tailWord_3198889).sum := by decide
  have hdescent : baseEnd_3198889 < baseStart_3198889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198979 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_3198979 : Nat := 118140960795 + 3198979 * 2 ^ 59
def prefixEnd_3198979 : Nat := 4983230072969 + 3 ^ 40 * 3198979 * 2
def baseEnd_3198979 : Nat := 1642613830639344713650669

theorem tailTrace_3198979 : CollatzResearch.WordTrace tailWord_3198979 prefixEnd_3198979 1642613830639344713650669 := by
  unfold tailWord_3198979
  simp only [CollatzResearch.WordTrace]
  refine ⟨116676349477652899961791991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77784232985101933307861327 116676349477652899961791991)
  ·
    refine ⟨175014524216479349942687987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116676349477652899961791991 175014524216479349942687987)
    ·
      refine ⟨262521786324719024914031981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175014524216479349942687987 262521786324719024914031981)
      ·
        refine ⟨98445669871769634342761993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262521786324719024914031981 98445669871769634342761993)
        ·
          refine ⟨73834252403827225757071495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98445669871769634342761993 73834252403827225757071495)
          ·
            refine ⟨110751378605740838635607243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73834252403827225757071495 110751378605740838635607243)
            ·
              refine ⟨166127067908611257953410865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110751378605740838635607243 166127067908611257953410865)
              ·
                refine ⟨124595300931458443465058149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166127067908611257953410865 124595300931458443465058149)
                ·
                  refine ⟨23361618924648458149698403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124595300931458443465058149 23361618924648458149698403)
                  ·
                    refine ⟨35042428386972687224547605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23361618924648458149698403 35042428386972687224547605)
                    ·
                      refine ⟨1642613830639344713650669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35042428386972687224547605 1642613830639344713650669)
                      ·
                        rfl

theorem cell23_3198979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_3198979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198979 prefixEnd_3198979 := by exact prefixLift 3198979
  have htrace : WordTrace (prefixWord ++ tailWord_3198979) baseStart_3198979 baseEnd_3198979 := by
    simpa [prefixWord, tailWord_3198979, baseEnd_3198979] using wordTrace_append hprefix tailTrace_3198979
  have hstable : (prefixWord ++ tailWord_3198979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198979).length < 2 ^ (prefixWord ++ tailWord_3198979).sum := by decide
  have hdescent : baseEnd_3198979 < baseStart_3198979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198983 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3198983 : Nat := 118140960795 + 3198983 * 2 ^ 59
def prefixEnd_3198983 : Nat := 4983230072969 + 3 ^ 40 * 3198983 * 2
def baseEnd_3198983 : Nat := 1642615884561962698000651

theorem tailTrace_3198983 : CollatzResearch.WordTrace tailWord_3198983 prefixEnd_3198983 1642615884561962698000651 := by
  unfold tailWord_3198983
  simp only [CollatzResearch.WordTrace]
  refine ⟨116676495369638408644937603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77784330246425605763291735 116676495369638408644937603)
  ·
    refine ⟨175014743054457612967406405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116676495369638408644937603 175014743054457612967406405)
    ·
      refine ⟨32815264322710802431388701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175014743054457612967406405 32815264322710802431388701)
      ·
        refine ⟨12305724121016550911770763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32815264322710802431388701 12305724121016550911770763)
        ·
          refine ⟨18458586181524826367656145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305724121016550911770763 18458586181524826367656145)
          ·
            refine ⟨13843939636143619775742109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18458586181524826367656145 13843939636143619775742109)
            ·
              refine ⟨5191477363553857415903291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13843939636143619775742109 5191477363553857415903291)
              ·
                refine ⟨7787216045330786123854937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191477363553857415903291 7787216045330786123854937)
                ·
                  refine ⟨5840412033998089592891203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787216045330786123854937 5840412033998089592891203)
                  ·
                    refine ⟨8760618050997134389336805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840412033998089592891203 8760618050997134389336805)
                    ·
                      refine ⟨1642615884561962698000651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8760618050997134389336805 1642615884561962698000651)
                      ·
                        rfl

theorem cell23_3198983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3198983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3198983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3198983 prefixEnd_3198983 := by exact prefixLift 3198983
  have htrace : WordTrace (prefixWord ++ tailWord_3198983) baseStart_3198983 baseEnd_3198983 := by
    simpa [prefixWord, tailWord_3198983, baseEnd_3198983] using wordTrace_append hprefix tailTrace_3198983
  have hstable : (prefixWord ++ tailWord_3198983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198983).length < 2 ^ (prefixWord ++ tailWord_3198983).sum := by decide
  have hdescent : baseEnd_3198983 < baseStart_3198983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199010 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3199010 : Nat := 118140960795 + 3199010 * 2 ^ 59
def prefixEnd_3199010 : Nat := 4983230072969 + 3 ^ 40 * 3199010 * 2
def baseEnd_3199010 : Nat := 547543249513211364121009

theorem tailTrace_3199010 : CollatzResearch.WordTrace tailWord_3199010 prefixEnd_3199010 547543249513211364121009 := by
  unfold tailWord_3199010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169370035135148064042621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77784986760360394837446989 29169370035135148064042621)
  ·
    refine ⟨10938513763175680524015983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29169370035135148064042621 10938513763175680524015983)
    ·
      refine ⟨16407770644763520786023975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10938513763175680524015983 16407770644763520786023975)
      ·
        refine ⟨24611655967145281179035963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16407770644763520786023975 24611655967145281179035963)
        ·
          refine ⟨36917483950717921768553945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24611655967145281179035963 36917483950717921768553945)
          ·
            refine ⟨27688112963038441326415459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36917483950717921768553945 27688112963038441326415459)
            ·
              refine ⟨41532169444557661989623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27688112963038441326415459 41532169444557661989623189)
              ·
                refine ⟨1946820442713640405763587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41532169444557661989623189 1946820442713640405763587)
                ·
                  refine ⟨2920230664070460608645381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946820442713640405763587 2920230664070460608645381)
                  ·
                    refine ⟨547543249513211364121009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920230664070460608645381 547543249513211364121009)
                    ·
                      rfl

theorem cell23_3199010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3199010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199010 prefixEnd_3199010 := by exact prefixLift 3199010
  have htrace : WordTrace (prefixWord ++ tailWord_3199010) baseStart_3199010 baseEnd_3199010 := by
    simpa [prefixWord, tailWord_3199010, baseEnd_3199010] using wordTrace_append hprefix tailTrace_3199010
  have hstable : (prefixWord ++ tailWord_3199010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199010).length < 2 ^ (prefixWord ++ tailWord_3199010).sum := by decide
  have hdescent : baseEnd_3199010 < baseStart_3199010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199019 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 9]
def baseStart_3199019 : Nat := 118140960795 + 3199019 * 2 ^ 59
def prefixEnd_3199019 : Nat := 4983230072969 + 3 ^ 40 * 3199019 * 2
def baseEnd_3199019 : Nat := 547544789955174852383495

theorem tailTrace_3199019 : CollatzResearch.WordTrace tailWord_3199019 prefixEnd_3199019 547544789955174852383495 := by
  unfold tailWord_3199019
  simp only [CollatzResearch.WordTrace]
  refine ⟨116677808397507986793248111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77785205598338657862165407 116677808397507986793248111)
  ·
    refine ⟨175016712596261980189872167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116677808397507986793248111 175016712596261980189872167)
    ·
      refine ⟨262525068894392970284808251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175016712596261980189872167 262525068894392970284808251)
      ·
        refine ⟨393787603341589455427212377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262525068894392970284808251 393787603341589455427212377)
        ·
          refine ⟨295340702506192091570409283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393787603341589455427212377 295340702506192091570409283)
          ·
            refine ⟨443011053759288137355613925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295340702506192091570409283 443011053759288137355613925)
            ·
              refine ⟨83064572579866525754177611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443011053759288137355613925 83064572579866525754177611)
              ·
                refine ⟨124596858869799788631266417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83064572579866525754177611 124596858869799788631266417)
                ·
                  refine ⟨93447644152349841473449813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124596858869799788631266417 93447644152349841473449813)
                  ·
                    refine ⟨547544789955174852383495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 93447644152349841473449813 547544789955174852383495)
                    ·
                      rfl

theorem cell23_3199019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_3199019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199019 prefixEnd_3199019 := by exact prefixLift 3199019
  have htrace : WordTrace (prefixWord ++ tailWord_3199019) baseStart_3199019 baseEnd_3199019 := by
    simpa [prefixWord, tailWord_3199019, baseEnd_3199019] using wordTrace_append hprefix tailTrace_3199019
  have hstable : (prefixWord ++ tailWord_3199019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199019).length < 2 ^ (prefixWord ++ tailWord_3199019).sum := by decide
  have hdescent : baseEnd_3199019 < baseStart_3199019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
