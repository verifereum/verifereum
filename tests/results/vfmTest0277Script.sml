Theory vfmTest0277[no_sig_docs]
Ancestors vfmTestDefs0277
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0277_0.nsv", "result0277_1.nsv", "result0277_2.nsv", "result0277_3.nsv", "result0277_4.nsv", "result0277_5.nsv", "result0277_6.nsv", "result0277_7.nsv", "result0277_8.nsv", "result0277_9.nsv", "result0277_10.nsv", "result0277_11.nsv", "result0277_12.nsv", "result0277_13.nsv", "result0277_14.nsv", "result0277_15.nsv", "result0277_16.nsv", "result0277_17.nsv", "result0277_18.nsv", "result0277_19.nsv", "result0277_20.nsv", "result0277_21.nsv", "result0277_22.nsv", "result0277_23.nsv", "result0277_24.nsv", "result0277_25.nsv", "result0277_26.nsv", "result0277_27.nsv", "result0277_28.nsv", "result0277_29.nsv"];
val thyn = "vfmTestDefs0277";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
