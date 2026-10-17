Theory vfmTest2276[no_sig_docs]
Ancestors vfmTestDefs2276
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2276_0.nsv", "result2276_1.nsv", "result2276_2.nsv", "result2276_3.nsv", "result2276_4.nsv", "result2276_5.nsv", "result2276_6.nsv", "result2276_7.nsv"];
val thyn = "vfmTestDefs2276";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
