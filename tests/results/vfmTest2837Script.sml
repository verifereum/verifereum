Theory vfmTest2837[no_sig_docs]
Ancestors vfmTestDefs2837
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2837_0.nsv", "result2837_1.nsv", "result2837_2.nsv", "result2837_3.nsv"];
val thyn = "vfmTestDefs2837";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
