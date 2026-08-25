Theory vfmTest0471[no_sig_docs]
Ancestors vfmTestDefs0471
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0471_0.nsv", "result0471_1.nsv", "result0471_2.nsv", "result0471_3.nsv", "result0471_4.nsv", "result0471_5.nsv", "result0471_6.nsv", "result0471_7.nsv", "result0471_8.nsv"];
val thyn = "vfmTestDefs0471";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
