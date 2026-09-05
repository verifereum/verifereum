Theory vfmTest0953[no_sig_docs]
Ancestors vfmTestDefs0953
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0953_0.nsv", "result0953_1.nsv", "result0953_2.nsv", "result0953_3.nsv", "result0953_4.nsv", "result0953_5.nsv", "result0953_6.nsv", "result0953_7.nsv", "result0953_8.nsv", "result0953_9.nsv", "result0953_10.nsv", "result0953_11.nsv", "result0953_12.nsv", "result0953_13.nsv", "result0953_14.nsv", "result0953_15.nsv", "result0953_16.nsv", "result0953_17.nsv", "result0953_18.nsv", "result0953_19.nsv", "result0953_20.nsv", "result0953_21.nsv", "result0953_22.nsv", "result0953_23.nsv", "result0953_24.nsv", "result0953_25.nsv", "result0953_26.nsv", "result0953_27.nsv", "result0953_28.nsv", "result0953_29.nsv", "result0953_30.nsv", "result0953_31.nsv", "result0953_32.nsv", "result0953_33.nsv", "result0953_34.nsv", "result0953_35.nsv", "result0953_36.nsv", "result0953_37.nsv", "result0953_38.nsv", "result0953_39.nsv", "result0953_40.nsv", "result0953_41.nsv"];
val thyn = "vfmTestDefs0953";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
