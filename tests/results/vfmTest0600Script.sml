Theory vfmTest0600[no_sig_docs]
Ancestors vfmTestDefs0600
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0600_0.nsv", "result0600_1.nsv", "result0600_2.nsv", "result0600_3.nsv", "result0600_4.nsv", "result0600_5.nsv", "result0600_6.nsv", "result0600_7.nsv", "result0600_8.nsv"];
val thyn = "vfmTestDefs0600";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
