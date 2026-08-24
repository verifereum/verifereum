Theory vfmTest0368[no_sig_docs]
Ancestors vfmTestDefs0368
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0368_0.nsv", "result0368_1.nsv", "result0368_2.nsv"];
val thyn = "vfmTestDefs0368";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
