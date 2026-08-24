Theory vfmTest2829[no_sig_docs]
Ancestors vfmTestDefs2829
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2829_0.nsv", "result2829_1.nsv", "result2829_2.nsv", "result2829_3.nsv"];
val thyn = "vfmTestDefs2829";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
