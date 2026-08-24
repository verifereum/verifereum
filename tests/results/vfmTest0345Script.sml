Theory vfmTest0345[no_sig_docs]
Ancestors vfmTestDefs0345
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0345_0.nsv", "result0345_1.nsv"];
val thyn = "vfmTestDefs0345";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
