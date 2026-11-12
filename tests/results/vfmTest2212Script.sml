Theory vfmTest2212[no_sig_docs]
Ancestors vfmTestDefs2212
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2212_0.nsv", "result2212_1.nsv", "result2212_2.nsv", "result2212_3.nsv", "result2212_4.nsv", "result2212_5.nsv", "result2212_6.nsv", "result2212_7.nsv", "result2212_8.nsv", "result2212_9.nsv", "result2212_10.nsv", "result2212_11.nsv", "result2212_12.nsv", "result2212_13.nsv", "result2212_14.nsv", "result2212_15.nsv", "result2212_16.nsv", "result2212_17.nsv", "result2212_18.nsv", "result2212_19.nsv"];
val thyn = "vfmTestDefs2212";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
