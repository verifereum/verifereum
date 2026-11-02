Theory vfmTest2975[no_sig_docs]
Ancestors vfmTestDefs2975
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2975_0.nsv", "result2975_1.nsv", "result2975_2.nsv"];
val thyn = "vfmTestDefs2975";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
