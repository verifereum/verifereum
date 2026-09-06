Theory vfmTest0118[no_sig_docs]
Ancestors vfmTestDefs0118
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0118_0.nsv", "result0118_1.nsv", "result0118_2.nsv"];
val thyn = "vfmTestDefs0118";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
