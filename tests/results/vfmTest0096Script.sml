Theory vfmTest0096[no_sig_docs]
Ancestors vfmTestDefs0096
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0096_0.nsv", "result0096_1.nsv", "result0096_2.nsv", "result0096_3.nsv"];
val thyn = "vfmTestDefs0096";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
