Theory vfmTest0548[no_sig_docs]
Ancestors vfmTestDefs0548
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0548_0.nsv", "result0548_1.nsv", "result0548_2.nsv", "result0548_3.nsv", "result0548_4.nsv", "result0548_5.nsv", "result0548_6.nsv", "result0548_7.nsv", "result0548_8.nsv"];
val thyn = "vfmTestDefs0548";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
