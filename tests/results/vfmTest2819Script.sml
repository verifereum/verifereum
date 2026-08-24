Theory vfmTest2819[no_sig_docs]
Ancestors vfmTestDefs2819
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2819_0.nsv", "result2819_1.nsv", "result2819_2.nsv", "result2819_3.nsv"];
val thyn = "vfmTestDefs2819";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
