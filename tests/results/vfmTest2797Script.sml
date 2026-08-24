Theory vfmTest2797[no_sig_docs]
Ancestors vfmTestDefs2797
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2797_0.nsv", "result2797_1.nsv", "result2797_2.nsv", "result2797_3.nsv"];
val thyn = "vfmTestDefs2797";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
