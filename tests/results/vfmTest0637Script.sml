Theory vfmTest0637[no_sig_docs]
Ancestors vfmTestDefs0637
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0637_0.nsv", "result0637_1.nsv", "result0637_2.nsv", "result0637_3.nsv", "result0637_4.nsv", "result0637_5.nsv", "result0637_6.nsv", "result0637_7.nsv"];
val thyn = "vfmTestDefs0637";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
