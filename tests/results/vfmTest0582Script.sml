Theory vfmTest0582[no_sig_docs]
Ancestors vfmTestDefs0582
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0582_0.nsv", "result0582_1.nsv", "result0582_2.nsv", "result0582_3.nsv", "result0582_4.nsv", "result0582_5.nsv", "result0582_6.nsv", "result0582_7.nsv"];
val thyn = "vfmTestDefs0582";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
