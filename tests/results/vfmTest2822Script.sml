Theory vfmTest2822[no_sig_docs]
Ancestors vfmTestDefs2822
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2822_0.nsv", "result2822_1.nsv", "result2822_2.nsv", "result2822_3.nsv"];
val thyn = "vfmTestDefs2822";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
