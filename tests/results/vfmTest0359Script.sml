Theory vfmTest0359[no_sig_docs]
Ancestors vfmTestDefs0359
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0359_0.nsv", "result0359_1.nsv", "result0359_2.nsv", "result0359_3.nsv", "result0359_4.nsv", "result0359_5.nsv", "result0359_6.nsv", "result0359_7.nsv", "result0359_8.nsv", "result0359_9.nsv", "result0359_10.nsv", "result0359_11.nsv", "result0359_12.nsv", "result0359_13.nsv", "result0359_14.nsv", "result0359_15.nsv", "result0359_16.nsv", "result0359_17.nsv", "result0359_18.nsv", "result0359_19.nsv", "result0359_20.nsv", "result0359_21.nsv", "result0359_22.nsv", "result0359_23.nsv", "result0359_24.nsv", "result0359_25.nsv", "result0359_26.nsv", "result0359_27.nsv", "result0359_28.nsv", "result0359_29.nsv", "result0359_30.nsv", "result0359_31.nsv", "result0359_32.nsv", "result0359_33.nsv", "result0359_34.nsv", "result0359_35.nsv", "result0359_36.nsv", "result0359_37.nsv", "result0359_38.nsv", "result0359_39.nsv", "result0359_40.nsv", "result0359_41.nsv", "result0359_42.nsv", "result0359_43.nsv", "result0359_44.nsv", "result0359_45.nsv", "result0359_46.nsv", "result0359_47.nsv", "result0359_48.nsv", "result0359_49.nsv", "result0359_50.nsv", "result0359_51.nsv"];
val thyn = "vfmTestDefs0359";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
