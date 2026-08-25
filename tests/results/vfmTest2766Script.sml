Theory vfmTest2766[no_sig_docs]
Ancestors vfmTestDefs2766
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2766_0.nsv", "result2766_1.nsv", "result2766_2.nsv", "result2766_3.nsv"];
val thyn = "vfmTestDefs2766";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
