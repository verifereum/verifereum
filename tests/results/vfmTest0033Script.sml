Theory vfmTest0033[no_sig_docs]
Ancestors vfmTestDefs0033
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0033_0.nsv", "result0033_1.nsv", "result0033_2.nsv", "result0033_3.nsv", "result0033_4.nsv", "result0033_5.nsv", "result0033_6.nsv", "result0033_7.nsv"];
val thyn = "vfmTestDefs0033";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
