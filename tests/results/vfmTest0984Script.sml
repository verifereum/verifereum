Theory vfmTest0984[no_sig_docs]
Ancestors vfmTestDefs0984
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0984_0.nsv", "result0984_1.nsv", "result0984_2.nsv", "result0984_3.nsv", "result0984_4.nsv"];
val thyn = "vfmTestDefs0984";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
