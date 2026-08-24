Theory vfmTest2769[no_sig_docs]
Ancestors vfmTestDefs2769
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2769_0.nsv", "result2769_1.nsv", "result2769_2.nsv", "result2769_3.nsv"];
val thyn = "vfmTestDefs2769";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
