Theory vfmTest0782[no_sig_docs]
Ancestors vfmTestDefs0782
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0782_0.nsv", "result0782_1.nsv", "result0782_2.nsv", "result0782_3.nsv"];
val thyn = "vfmTestDefs0782";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
