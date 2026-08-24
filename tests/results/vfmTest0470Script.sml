Theory vfmTest0470[no_sig_docs]
Ancestors vfmTestDefs0470
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0470_0.nsv", "result0470_1.nsv", "result0470_2.nsv", "result0470_3.nsv", "result0470_4.nsv", "result0470_5.nsv", "result0470_6.nsv", "result0470_7.nsv"];
val thyn = "vfmTestDefs0470";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
