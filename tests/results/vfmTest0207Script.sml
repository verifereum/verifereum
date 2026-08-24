Theory vfmTest0207[no_sig_docs]
Ancestors vfmTestDefs0207
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0207_0.nsv", "result0207_1.nsv", "result0207_2.nsv", "result0207_3.nsv", "result0207_4.nsv", "result0207_5.nsv"];
val thyn = "vfmTestDefs0207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
