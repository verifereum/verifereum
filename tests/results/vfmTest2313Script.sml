Theory vfmTest2313[no_sig_docs]
Ancestors vfmTestDefs2313
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2313_0.nsv", "result2313_1.nsv", "result2313_2.nsv", "result2313_3.nsv", "result2313_4.nsv", "result2313_5.nsv", "result2313_6.nsv", "result2313_7.nsv", "result2313_8.nsv", "result2313_9.nsv", "result2313_10.nsv", "result2313_11.nsv", "result2313_12.nsv", "result2313_13.nsv", "result2313_14.nsv", "result2313_15.nsv", "result2313_16.nsv", "result2313_17.nsv", "result2313_18.nsv", "result2313_19.nsv", "result2313_20.nsv", "result2313_21.nsv"];
val thyn = "vfmTestDefs2313";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
