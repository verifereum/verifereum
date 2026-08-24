Theory vfmTest2720[no_sig_docs]
Ancestors vfmTestDefs2720
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2720_0.nsv", "result2720_1.nsv", "result2720_2.nsv", "result2720_3.nsv"];
val thyn = "vfmTestDefs2720";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
