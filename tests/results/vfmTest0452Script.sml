Theory vfmTest0452[no_sig_docs]
Ancestors vfmTestDefs0452
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0452_0.nsv", "result0452_1.nsv", "result0452_2.nsv", "result0452_3.nsv"];
val thyn = "vfmTestDefs0452";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
