Theory vfmTest0312[no_sig_docs]
Ancestors vfmTestDefs0312
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0312_0.nsv", "result0312_1.nsv"];
val thyn = "vfmTestDefs0312";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
