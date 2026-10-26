Theory vfmTest0580[no_sig_docs]
Ancestors vfmTestDefs0580
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0580_0.nsv", "result0580_1.nsv", "result0580_2.nsv", "result0580_3.nsv", "result0580_4.nsv", "result0580_5.nsv", "result0580_6.nsv", "result0580_7.nsv"];
val thyn = "vfmTestDefs0580";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
