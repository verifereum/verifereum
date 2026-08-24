Theory vfmTest2301[no_sig_docs]
Ancestors vfmTestDefs2301
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2301_0.nsv", "result2301_1.nsv"];
val thyn = "vfmTestDefs2301";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
