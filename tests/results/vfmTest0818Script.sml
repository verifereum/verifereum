Theory vfmTest0818[no_sig_docs]
Ancestors vfmTestDefs0818
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0818_0.nsv", "result0818_1.nsv", "result0818_2.nsv", "result0818_3.nsv", "result0818_4.nsv", "result0818_5.nsv", "result0818_6.nsv", "result0818_7.nsv"];
val thyn = "vfmTestDefs0818";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
