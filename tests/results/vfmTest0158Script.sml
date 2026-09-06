Theory vfmTest0158[no_sig_docs]
Ancestors vfmTestDefs0158
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0158_0.nsv", "result0158_1.nsv", "result0158_2.nsv", "result0158_3.nsv"];
val thyn = "vfmTestDefs0158";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
