Theory vfmTest2237[no_sig_docs]
Ancestors vfmTestDefs2237
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2237_0.nsv", "result2237_1.nsv", "result2237_2.nsv", "result2237_3.nsv", "result2237_4.nsv", "result2237_5.nsv", "result2237_6.nsv", "result2237_7.nsv", "result2237_8.nsv", "result2237_9.nsv", "result2237_10.nsv", "result2237_11.nsv"];
val thyn = "vfmTestDefs2237";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
